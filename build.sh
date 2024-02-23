#!/bin/bash

# to run the build with tests, add the "-t" option. For instance, instead of running "build.sh", run "build.sh -t".

SCRIPTNAME="walnut.sh"

if [[ $1 = "-t" ]]; then
	# run with tests
	echo "Building Walnut and running tests."
	./gradlew clean build test jacocoTestReport customFatJar
else
	# If you want a fast build without tests, you can run:
	echo "Building Walnut. To run tests, add the -t flag to the command."
	./gradlew clean customFatJar
fi	

chmod +x $SCRIPTNAME

read -p "Press enter to continue"