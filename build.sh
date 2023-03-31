#!/bin/bash

./gradlew clean build test jacocoTestReport customFatJar

# If you want a fast build without tests, you can run:
# ./gradlew clean customFatJar

read -p "Press enter to continue"
