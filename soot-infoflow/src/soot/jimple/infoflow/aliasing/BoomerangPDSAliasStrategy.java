package soot.jimple.infoflow.aliasing;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Multimap;

import boomerang.BackwardQuery;
import boomerang.Boomerang;
import boomerang.jimple.Field;
import boomerang.jimple.Statement;
import boomerang.jimple.Val;
import boomerang.results.BackwardBoomerangResults;
import heros.solver.Pair;
import soot.Local;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.AccessPath;
import soot.jimple.infoflow.solver.IInfoflowSolver;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import wpds.impl.Weight.NoWeight;

/**
 * A fully flow-sensitive aliasing strategy
 * 
 * @author Johannes Spaeth
 */
public class BoomerangPDSAliasStrategy extends AbstractBulkAliasStrategy {

	private Multimap<Pair<SootMethod, Abstraction>, Pair<Unit, Abstraction>> incomingMap = HashMultimap.create();

	public BoomerangPDSAliasStrategy(InfoflowManager manager) {
		super(manager);
	}

	@Override
	public void computeAliasTaints(final Abstraction d1, final Stmt src, final Value targetValue,
			Set<Abstraction> taintSet, SootMethod method, Abstraction newAbs) {
		// Start the backwards solver
		Abstraction bwAbs = newAbs.deriveInactiveAbstraction(src);
		AccessPath accessPath = bwAbs.getAccessPath();
		Local base = newAbs.getAccessPath().getPlainValue();

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
		Boomerang boomerang = new Boomerang() {
			@Override
			public BiDiInterproceduralCFG<Unit, SootMethod> icfg() {
				return manager.getICFG();
			}
		};
		SootMethod queryMethod = manager.getICFG().getMethodOf(src);
		for (Unit pred : manager.getICFG().getPredsOf(src)) {
			Statement queryStatement = new Statement((Stmt) pred, queryMethod);
			BackwardQuery backwardQuery = new BackwardQuery(queryStatement, new Val(base, queryMethod), accessPath);
			System.out.println(src + "   " + backwardQuery + accessPath);
			BackwardBoomerangResults<NoWeight> results = boomerang.solve(backwardQuery);
			Set<boomerang.util.AccessPath> boomerangResults = results.getAllAliases();
			System.out.println(src + "   " + boomerangResults);
			for (boomerang.util.AccessPath boomerangAp : boomerangResults) {
				Abstraction flowDroidAccessPath = toAbstraction(boomerangAp, src, newAbs);
				// add all access path to the taintSet for further propagation
				if (flowDroidAccessPath != null)
					taintSet.add(flowDroidAccessPath);
			}
		}
	}

	private void handleFieldWrite(Abstraction d1, Stmt src, Set<Abstraction> taintSet, Abstraction newAbs, Local base,
			List<Field> fields) {
		if (base == null) {
			System.out.println("Base is null: " + base + src);
			return;
		}

		Boomerang boomerang = new Boomerang() {
			@Override
			public BiDiInterproceduralCFG<Unit, SootMethod> icfg() {
				return manager.getICFG();
			}
		};
		SootMethod queryMethod = manager.getICFG().getMethodOf(src);
		Statement queryStatement = new Statement(src, queryMethod);
		BackwardQuery backwardQuery = new BackwardQuery(queryStatement, new Val(base, queryMethod));
		BackwardBoomerangResults<NoWeight> results = boomerang.solve(backwardQuery);
		Set<boomerang.util.AccessPath> boomerangResults = results.getAllAliases();
		System.out.println(src + "   " + boomerangResults);
		for (boomerang.util.AccessPath boomerangAp : boomerangResults) {
			Abstraction flowDroidAccessPath = toAbstraction(boomerangAp, src, newAbs);
			// add all access path to the taintSet for further propagation
			if (flowDroidAccessPath != null)
				taintSet.add(flowDroidAccessPath);
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
	}

}
