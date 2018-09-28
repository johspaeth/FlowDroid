#!/usr/bin/python

import sys, os,subprocess
from subprocess import call
from multiprocessing import Process, Pool

APK_FOLDER = "FlowDroid-APKs"
ANDROID_PLATFORM_PATH = "D:\android-sdk\platforms"
JAR = "soot-infoflow-android-classes.jar"

dacapo = ["antlr", 
	"chart",
	"eclipse",
	"hsqldb",
	"jython",
	"luindex",
	"lusearch",
	"pmd", 
	"fop",
	"xalan", 
	"bloat" 
];
analyses = [
#"flowsensitive",
"boomerang",
#"da",
"sb" ,
"default"
];
;

def runAnalysis(arg):
	print("Analyzing " + arg[0] +" : " + arg[1])
	f = open("outputFD-logs/log-" + arg[0] +" - " + arg[1] +".txt", "w")
	call(["java","-DoutputFile="+arg[0], "-Xmx12g","-Xss164m","-cp", JAR, "boomerang.experiments.Main",ANDROID_PLATFORM_PATH, arg[1], arg[2]],  stdout=f,stderr=subprocess.STDOUT, timeout=60*60*36)
 
args = []
directory = os.fsencode(APK_FOLDER)

for file in os.listdir(directory):
    filename = os.fsdecode(file)
    if filename.endswith(".apk"): 
		for analysis in analyses:
			args.append([filename,  analysis])

if __name__ == '__main__':
	with Pool(8) as p:
		p.map(runAnalysis, args)
		
