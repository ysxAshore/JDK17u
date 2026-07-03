# Welcome to OpenJDK 17 Updates!

The JDK 17 Updates project uses two GitHub repositories.
Updates are continuously developed in the repository [jdk17u-dev](https://github.com/openjdk/jdk17u-dev). This is the repository usually targeted by contributors.
The [jdk17u](https://github.com/openjdk/jdk17u) repository is used for rampdown of the update releases of jdk17u and only accepts critical changes that must make the next release during rampdown. (You probably do not want to target jdk17u).

For more OpenJDK 17 updates specific information such as timelines and contribution guidelines see the [project wiki page](https://wiki.openjdk.org/display/JDKUpdates/JDK+17u/).


For build instructions please see the
[online documentation](https://openjdk.java.net/groups/build/doc/building.html),
or either of these files:

- [doc/building.html](doc/building.html) (html version)
- [doc/building.md](doc/building.md) (markdown version)

See <https://openjdk.java.net/> for more information about
the OpenJDK Community and the JDK.

./build/linux-x86_64-server-release/jdk/bin/java -Xlog:gc+task -XX:+UseG1GC -XX:-UseCompressedOops -XX:-UseCompressedClassPointers -XX:ParallelGCThreads=2 -XX:ConcGCThreads=2 -jar ../../test/benchmark/dacapo/dacapo-23.11-MR2-chopin.jar avrora
