##  Build process

Walnut is currently built with the [Gradle](https://gradle.org) build system, and supports:
- unit testing via [JUnit](https://junit.org)
  - integration testing is done via the unit testing process, to show code coverage
- code coverage reports via [JaCoCo](https://jacoco.org/jacoco/)
- static analysis via [SpotBugs](https://spotbugs.github.io/)
  - Disabled by default, since it flags a few issues which fail the build. Uncomment the SpotBugs code in the `build.gradle` file to enable. 

To build Walnut, run `build.sh`. This creates both "thin" and "fat" [JAR](https://en.wikipedia.org/wiki/JAR_(file_format)) files. The fat JAR (Walnut-all.jar) packages up dependent libraries which are necessary for execution. 

To run Walnut, run `run_walnut.sh.` This executes the JAR.

## Libraries

Walnut uses the following libraries:
- [fastutil](https://github.com/vigna/fastutil): memory-efficient collections
- [dk.brics.automaton](https://brics.dk/automaton/) - DFA/NFA implementation
  - Much of this is not used; this library uses `char` primitives for states,which would mean a limit of 65536 states
