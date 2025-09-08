.PHONY: all clean tlc-safety-small tlc-safety-fast tlc-safety-slow download-tla

TLA_VERSION := 1.8.0
TLA_JAR := tla2tools.jar
TLA_URL := https://github.com/tlaplus/tlaplus/releases/download/v$(TLA_VERSION)/tla2tools.jar

all: tlc-safety-small

$(TLA_JAR):
	@echo "Downloading TLA+ tools..."
	curl -L -o $(TLA_JAR) $(TLA_URL)

download-tla: $(TLA_JAR)

tlc-safety-small: $(TLA_JAR)
	@echo "Running TLC on safety_small_4 model..."
	@echo "Validators: v1(10%), v2(20%), v3(30%), v4(40%)"
	@echo "Checking invariants: NoDoubleFinalization, CertUnique, NoEquivocation"
	java -XX:+UseParallelGC -cp $(TLA_JAR) tlc2.TLC \
		-config models/safety_small_4.cfg \
		-modelcheck \
		-deadlock \
		-fp 64 \
		-workers auto \
		specs/tla/SafetyInvariants.tla

tlc-safety-fast: $(TLA_JAR)
	@echo "Running TLC on fast path model (100% participation -> 80%+ fast finalization)..."
	@echo "Active validators: All (100% stake)"
	java -XX:+UseParallelGC -cp $(TLA_JAR) tlc2.TLC \
		-config models/safety_fast_4.cfg \
		-modelcheck \
		-deadlock \
		-fp 64 \
		-workers auto \
		specs/tla/SafetyInvariants.tla

tlc-safety-slow: $(TLA_JAR)
	@echo "Running TLC on slow path model (70% participation -> regular finalization)..."
	@echo "Active validators: v1(10%) + v2(20%) + v4(40%) = 70% stake"
	java -XX:+UseParallelGC -cp $(TLA_JAR) tlc2.TLC \
		-config models/safety_slow_4.cfg \
		-modelcheck \
		-deadlock \
		-fp 64 \
		-workers auto \
		specs/tla/SafetyInvariants.tla

clean:
	rm -rf states/
	rm -f *.out
	rm -f specs/tla/*.old
	find . -name "*.dump" -delete