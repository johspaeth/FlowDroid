package soot.jimple.infoflow.aliasing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;
import com.google.common.collect.Sets;

import boomerang.BackwardQuery;
import boomerang.Boomerang;
import boomerang.Context;
import boomerang.DefaultBoomerangOptions;
import boomerang.ForwardQuery;
import boomerang.IContextRequester;
import boomerang.jimple.Field;
import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import boomerang.results.AbstractBoomerangResults;
import boomerang.results.BackwardBoomerangResults;
import boomerang.results.ExtractAllAliasListener;
import boomerang.solver.AbstractBoomerangSolver;
import heros.InterproceduralCFG;
import heros.solver.Pair;
import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.solver.IInfoflowSolver;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import sync.pds.solver.nodes.INode;
import sync.pds.solver.nodes.SingleNode;
import wpds.impl.StackListener;
import wpds.impl.Weight.NoWeight;

/**
 * A fully flow-sensitive aliasing strategy
 * 
 * @author Johannes Spaeth
 */
public class BoomerangPDSAliasStrategy extends AbstractBulkAliasStrategy {

	private Multimap<Pair<SootMethod, Abstraction>, Pair<Unit, Abstraction>> incomingMap = HashMultimap.create();
	private Boomerang boomerang;
	private Multimap<Statement, QueryWithAccessPath> aliasesAtCallSite = HashMultimap.create();
	private Abstraction zeroValue;

	public BoomerangPDSAliasStrategy(final InfoflowManager manager) {
		super(manager);
		System.out.println("SEEETING UP BOOMERANG");
		boomerang = new Boomerang(new DefaultBoomerangOptions() {
			@Override
			public int analysisTimeoutMS() {
				return Infoflow.aliasTimeoutInMilliSeconds;
			}
		}) {
			@Override
			public BiDiInterproceduralCFG<Unit, SootMethod> icfg() {
				return manager.getICFG();
			}

		};
		System.out.println("END UP BOOMERANG");

	}

	@Override
	public void computeAliasTaints(final Abstraction d1, final Stmt src, final Value targetValue,
			Set<Abstraction> taintSet, SootMethod method, Abstraction newAbs) {
		if (zeroValue == null && manager.getForwardSolver() != null
				&& manager.getForwardSolver().getTabulationProblem() != null)
			zeroValue = BoomerangPDSAliasStrategy.this.manager.getForwardSolver().getTabulationProblem()
					.createZeroValue();
		// Start the backwards solver
		Abstraction bwAbs = newAbs.deriveInactiveAbstraction(src);
		AccessPath accessPath = bwAbs.getAccessPath();
		Local base = newAbs.getAccessPath().getPlainValue();

		System.out.println("TRIGGER ");
		// There are two different queries necessary: At field writes and at method
		// return statements,
		// when there might be new alias in the caller scope.
		if (src.containsInvokeExpr())
			handleReturn(d1, src, taintSet, newAbs, base, convert(accessPath));
		else
			handleFieldWrite(d1, src, taintSet, newAbs, base, convert(accessPath));
	}

	private List<Field> convert(AccessPath accessPath) {
		List<Field> fields = Lists.newArrayList();
		if (accessPath != null && accessPath.getFieldCount() > 0) {
			for (SootField f : accessPath.getFields()) {
				fields.add(new Field(f));
			}
		}
		fields.add(Field.empty());
		return fields;
	}

	private void handleReturn(Abstraction d1, Stmt src, Set<Abstraction> taintSet, Abstraction newAbs, Local base,
			List<Field> accessPath) {
		if (base == null) {
			System.out.println("Base is null: " + base + src);
			return;
		}
		Statement callSite = new Statement((Stmt) src, manager.getICFG().getMethodOf(src));
		for (QueryWithAccessPath alloc : aliasesAtCallSite.get(callSite)) {
			AbstractBoomerangSolver<NoWeight> solver = boomerang.getSolvers().get(alloc.forwardQuery);
			Set<boomerang.util.AccessPath> aliases = Sets.newHashSet();
			System.out.println("REGISTER ON RETURN BOOMERANG ");

			long before = System.currentTimeMillis();
			solver.registerListener(new ExtractAllAliasListener<>(solver, aliases, callSite));
			long after = System.currentTimeMillis();
			Infoflow.aliasQueryTime += (after - before);
			for (boomerang.util.AccessPath boomerangAp : aliases) {
				if (solver.valueUsedInStatement(src, boomerangAp.getBase())) {
					continue;
				}
				Abstraction flowDroidAccessPath = toAbstraction(boomerangAp, src, alloc.accessPath);
				// add all access path to the taintSet for further propagation
				if (flowDroidAccessPath != null)
					taintSet.add(flowDroidAccessPath);
			}
			System.out.println("FINISHED ON RETURN BOOMERANG ");
		}
	}

	private void handleFieldWrite(Abstraction d1, Stmt src, Set<Abstraction> taintSet, final Abstraction newAbs,
			Local base, List<Field> fields) {
		if (base == null) {
			System.out.println("Base is null: " + base + src);
			return;
		}

		SootMethod queryMethod = manager.getICFG().getMethodOf(src);
		Statement queryStatement = new Statement(src, queryMethod);
		Val queryVal = new Val(base, queryMethod);
		BackwardQuery backwardQuery = new BackwardQuery(queryStatement, queryVal);
		System.out.println("START BOOMERANG " + backwardQuery);

		Infoflow.aliasQueryCounter++;
		long before = System.currentTimeMillis();
		BackwardBoomerangResults<NoWeight> results = boomerang.backwardSolveUnderScope(backwardQuery,
				new FlowDroidContextRequestor(d1));
		if (results.isTimedout())
			Infoflow.aliasQueryCounterTimeout++;
		System.out.println("FINISHED BOOMERANG ");
		for (final Entry<ForwardQuery, AbstractBoomerangResults<NoWeight>.Context> e : results.getAllocationSites()
				.entrySet()) {
			final AbstractBoomerangSolver<NoWeight> s = boomerang.getSolvers().get(e.getKey());
			s.getCallAutomaton().registerListener(new StackListener<Statement, INode<Val>, NoWeight>(
					s.getCallAutomaton(), new SingleNode<Val>(queryVal), queryStatement) {

				@Override
				public void anyContext(Statement end) {
				}

				@Override
				public void stackElement(Statement parent) {
					for (Statement cs : s.getPredsOf(parent)) {
						aliasesAtCallSite.put(cs, new QueryWithAccessPath(e.getKey(), newAbs));
					}
				}
			});
		}
		System.out.println("GET ALL ALIASEs ON WRITE BOOMERANG ");
		Set<boomerang.util.AccessPath> boomerangResults = results.getAllAliases();
		long after = System.currentTimeMillis();
		Infoflow.aliasQueryTime += (after - before);
		System.out.println("FINISHED ALL ALIASEs ON WRITE BOOMERANG ");
		for (boomerang.util.AccessPath boomerangAp : boomerangResults) {
			if (boomerangAp.getBase().equals(queryVal))
				continue;
			Abstraction flowDroidAccessPath = toAbstraction(boomerangAp, src, newAbs);
			// add all access path to the taintSet for further propagation
			if (flowDroidAccessPath != null)
				taintSet.add(flowDroidAccessPath);
		}
	}

	private class QueryWithAccessPath {
		final ForwardQuery forwardQuery;
		final Abstraction accessPath;

		public QueryWithAccessPath(ForwardQuery q, Abstraction newAbs) {
			this.forwardQuery = q;
			this.accessPath = newAbs;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((accessPath == null) ? 0 : accessPath.hashCode());
			result = prime * result + ((forwardQuery == null) ? 0 : forwardQuery.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			QueryWithAccessPath other = (QueryWithAccessPath) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (accessPath == null) {
				if (other.accessPath != null)
					return false;
			} else if (!accessPath.equals(other.accessPath))
				return false;
			if (forwardQuery == null) {
				if (other.forwardQuery != null)
					return false;
			} else if (!forwardQuery.equals(other.forwardQuery))
				return false;
			return true;
		}

		private BoomerangPDSAliasStrategy getOuterType() {
			return BoomerangPDSAliasStrategy.this;
		}
	}

	private Abstraction toAbstraction(boomerang.util.AccessPath ap, Stmt src, Abstraction newAbs) {
		Local base = ap.getBase().isStatic() ? null : (Local) ap.getBase().value();
		AccessPath fdAp = newAbs.getAccessPath();
		if (ap.getFields().isEmpty() && !ap.getBase().isStatic()) {
			return newAbs.deriveNewAbstraction(
					manager.getAccessPathFactory().createAccessPath(base, fdAp.getFields(), fdAp.getBaseType(),
							fdAp.getFieldTypes(), fdAp.getTaintSubFields(), false, false, fdAp.getArrayTaintType()),
					src);
		}
		if (ap.isOverApproximated()) {

		} else {
			Collection<Field> boomerangFields = ap.getFields();
			ArrayList<SootField> fdFields = new ArrayList<>();
			ArrayList<Type> fdFieldTypes = new ArrayList<>();
			if (ap.getBase().isStatic()) {
				StaticFieldRef ref = (StaticFieldRef) ap.getBase().value();
				fdFields.add(ref.getField());
				fdFieldTypes.add(ref.getField().getType());
			}
			for (Field f : boomerangFields) {
				if (f.equals(Field.array()) || f.equals(Field.empty()) || f.equals(Field.epsilon()))
					continue;
				fdFields.add(f.getSootField());
				fdFieldTypes.add(f.getSootField().getType());
			}
			if (fdAp.getFieldCount() > 0) {
				for (SootField f : fdAp.getFields()) {
					fdFields.add(f);
				}
				for (Type f : fdAp.getFieldTypes()) {
					fdFieldTypes.add(f);
				}
			}
			return newAbs.deriveNewAbstraction(
					manager.getAccessPathFactory().createAccessPath(base, fdFields.toArray(new SootField[] {}),
							(base != null ? base.getType() : null), fdFieldTypes.toArray(new Type[] {}),
							fdAp.getTaintSubFields(), false, false, fdAp.getArrayTaintType()),
					src);
		}
		// Collection<Field> fields = ap.getFields();
		// ArrayList<SootField> fdFields = new ArrayList<>();
		// ArrayList<Type> fdFieldType = new ArrayList<>();
		// int accessPathLength = manager.getAccessPathFactory();
		//
		// manager.getAccessPathFactory().create.createAccessPath();
		// for (int i = 0; i < Math.min(fields.size(), accessPathLength); i++) {
		// WrappedSootField field = fields[i];
		// if (field.getField().equals(AliasFinder.ARRAY_FIELD)) {
		// // throw new
		// // RuntimeException("TODO implement mappind of array to FlowDroid");
		// if (!fdFieldType.isEmpty()) {
		// int last = fdFieldType.size() - 1;
		// Type type = fdFieldType.get(last);
		// Type buildArrayOrAddDimension = buildArrayOrAddDimension(type);
		// fdFieldType.remove(last);
		// fdFieldType.add(buildArrayOrAddDimension);
		// }
		// } else {
		// fdFields.add(field.getField());
		// fdFieldType.add(field.getField().getType());
		// }
		// }
		// Type[] fdFieldTypeArray = fdFieldType.toArray(new Type[] {});
		// SootField[] fdFieldArray = fdFields.toArray(new SootField[] {});
		//
		// Value plainValue = ap.getBase();
		// Type baseType = null;
		// if (plainValue != null)
		// baseType = plainValue.getType();
		//
		// if (plainValue == null && fdFields.isEmpty())
		return null;
		// return newAbs
		// .deriveNewAbstraction(
		// new soot.jimple.infoflow.data.AccessPath(plainValue, fdFieldArray, baseType,
		// fdFieldTypeArray,
		// (newAbs.getAccessPath().isCutOffApproximation() || fields.length >
		// accessPathLength)),
		// src);
	}

	@Override
	public void injectCallingContext(Abstraction d3, IInfoflowSolver fSolver, SootMethod callee, Unit callSite,
			Abstraction source, Abstraction d1) {
		// This is called whenever something is added to the incoming set of the forward
		// solver of the
		// FlowDroid IFDS solver.
		Pair<SootMethod, Abstraction> calleepair = new Pair<>(callee, d3);
		Pair<Unit, Abstraction> callerpair = new Pair<>(callSite, d1);
		incomingMap.put(calleepair, callerpair);
	}

	@Override
	public boolean isFlowSensitive() {
		return true;
	}

	@Override
	public boolean requiresAnalysisOnReturn() {
		return true;
	}

	@Override
	public IInfoflowSolver getSolver() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void cleanup() {
		incomingMap.clear();
		boomerang = null;
		aliasesAtCallSite.clear();
		aliasesAtCallSite = null;
	}

	private class FlowDroidContextRequestor implements IContextRequester {
		private final Abstraction d1;
		private InterproceduralCFG<Unit, SootMethod> icfg;

		private FlowDroidContextRequestor(Abstraction d1) {
			this.d1 = d1;
			this.icfg = BoomerangPDSAliasStrategy.this.manager.getICFG();
		}

		@Override
		public Collection<Context> getCallSiteOf(Context c) {
			if (!(c instanceof FlowDroidContext)) {
				throw new RuntimeException("Context must be an instanceof FlowDroidContext");
			}

			FlowDroidContext cont = (FlowDroidContext) c;
			Statement callSite = cont.getStmt();
			Abstraction abstraction = cont.getAbstraction();
			Set<Context> boomerangCallerContexts = new HashSet<>();

			// If we did not has the 0-Fact as start fact, we query the incomingMap to see
			// via which
			// callsite the forward analysis entered a method
			Collection<Pair<Unit, Abstraction>> callerContexts = incomingMap
					.get(new Pair<SootMethod, Abstraction>(callSite.getMethod(), abstraction));

			for (Pair<Unit, Abstraction> callerContext : callerContexts) {
				SootMethod calleeMethod = icfg.getMethodOf(callerContext.getO1());
				if (isIgnoredMethod(calleeMethod))
					continue;
				Statement calleeStatement = new Statement((Stmt) callerContext.getO1(), calleeMethod);
				FlowDroidContext newContext = new FlowDroidContext(calleeStatement, callerContext.getO2());
				boomerangCallerContexts.add(newContext);
			}
			return boomerangCallerContexts;
		}

		@Override
		public Context initialContext(Statement stmt) {
			return new FlowDroidContext(stmt, d1);
		}

	}

	private class FlowDroidContext implements Context {
		private Statement stmt;
		private Abstraction abs;
		private SootMethod method;

		public FlowDroidContext(Statement stmt, Abstraction abs) {
			this.stmt = stmt;
			this.abs = abs;
		}

		public Abstraction getAbstraction() {
			return abs;
		}

		@Override
		public Statement getStmt() {
			return stmt;
		}

		public String toString() {
			return "FDContext[" + stmt + ", " + abs + "," + method + "]";
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((abs == null) ? 0 : abs.hashCode());
			result = prime * result + ((stmt == null) ? 0 : stmt.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			FlowDroidContext other = (FlowDroidContext) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (abs == null) {
				if (other.abs != null)
					return false;
			} else if (!abs.equals(other.abs))
				return false;
			if (stmt == null) {
				if (other.stmt != null)
					return false;
			} else if (!stmt.equals(other.stmt))
				return false;
			return true;
		}

		private BoomerangPDSAliasStrategy getOuterType() {
			return BoomerangPDSAliasStrategy.this;
		}

	}

	public boolean isIgnoredMethod(SootMethod methodOf) {
		return false;
	}
}
