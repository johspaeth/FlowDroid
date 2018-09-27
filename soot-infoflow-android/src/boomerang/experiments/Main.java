package boomerang.experiments;

import java.io.File;
import java.io.IOException;

import org.xmlpull.v1.XmlPullParserException;

import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;

public class Main {
	public static void main(String... args) throws IOException, XmlPullParserException {
		SetupApplication setupApplication = new SetupApplication(args[0], args[1]);

		// Find the taint wrapper file
		File taintWrapperFile = new File("EasyTaintWrapperSource.txt");
		if (!taintWrapperFile.exists())
			taintWrapperFile = new File("../soot-infoflow/EasyTaintWrapperSource.txt");
		setupApplication.setTaintWrapper(new EasyTaintWrapper(taintWrapperFile));
		setupApplication.getConfig().setUseRecursiveAccessPaths(false);
		setupApplication.getConfig().setUseThisChainReduction(false);
		setupApplication.getConfig().setAccessPathLength(5);
		// Configure the analysis
		setupApplication.runInfoflow("SourcesAndSinks.txt");
	}

}
