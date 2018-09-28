package boomerang.experiments;

import java.io.File;
import java.io.IOException;

import org.xmlpull.v1.XmlPullParserException;

import soot.jimple.infoflow.InfoflowConfiguration.AliasingAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.PathBuildingAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.PathReconstructionMode;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;

public class Main {

	public AliasingAlgorithm[] aliasAlgos = new AliasingAlgorithm[] { AliasingAlgorithm.FlowSensitive,
			AliasingAlgorithm.Boomerang, AliasingAlgorithm.DA, AliasingAlgorithm.SB };

	public static void main(String... args) throws IOException, XmlPullParserException {
		if (args.length != 3) {
			System.out.println("Usage:");
			System.out.println("PATH_TO_ANDROID_PLATFORMS PATH_TO_APK ALIAS_STRATEGY");
			return;
		}
		SetupApplication setupApplication = new SetupApplication(args[0], args[1]);

		// Find the taint wrapper file
		File taintWrapperFile = new File("EasyTaintWrapperSource.txt");
		String aliasAlgo = args[2];
		setupApplication.setTaintWrapper(new EasyTaintWrapper(taintWrapperFile));
		setupApplication.getConfig().setMaxThreadNum(1);
		setupApplication.getConfig().getSolverConfiguration().setMaxCalleesPerCallSite(-1);
		setupApplication.getConfig().setIgnoreFlowsInSystemPackages(false);
		setupApplication.getConfig().getPathConfiguration().setPathReconstructionMode(PathReconstructionMode.NoPaths);
		setupApplication.getConfig().getPathConfiguration().setPathBuildingAlgorithm(PathBuildingAlgorithm.None);
		setupApplication.getConfig().setCallgraphAlgorithm(CallgraphAlgorithm.SPARK);
		if (aliasAlgo.equalsIgnoreCase("default")) {
			setupApplication.runInfoflow("SourcesAndSinks.txt");
			return;
		}
		setupApplication.getConfig().setUseRecursiveAccessPaths(false);
		setupApplication.getConfig().setUseThisChainReduction(false);

		if (aliasAlgo.equalsIgnoreCase("Boomerang")) {
			setupApplication.getConfig().setAliasingAlgorithm(AliasingAlgorithm.Boomerang);
		} else if (aliasAlgo.equalsIgnoreCase("DA")) {
			setupApplication.getConfig().setFlowSensitiveAliasing(false);
			setupApplication.getConfig().setAliasingAlgorithm(AliasingAlgorithm.DA);
		} else if (aliasAlgo.equalsIgnoreCase("SB")) {
			setupApplication.getConfig().setFlowSensitiveAliasing(false);
			setupApplication.getConfig().setAliasingAlgorithm(AliasingAlgorithm.SB);
		} else if (aliasAlgo.equalsIgnoreCase("flowsensitive")) {
			setupApplication.getConfig().setAliasingAlgorithm(AliasingAlgorithm.FlowSensitive);
			setupApplication.getConfig().setAccessPathLength(5);
		}

		// Configure the analysis
		setupApplication.runInfoflow("SourcesAndSinks.txt");
	}

}
