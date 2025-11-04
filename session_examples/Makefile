MODULE_NAME ?= top
TOP_MODULE ?= $(MODULE_NAME)
VERILATOR_FLAGS ?= --top $(MODULE_NAME) -j 1

TEST_DRIVER = sim_main.cpp

all: obj_dir/V$(MODULE_NAME)

.PHONY: run clean

ANVIL_FLAGS= --
ifdef LTOFF
    ANVIL_FLAGS += -disable-lt-checks
endif

ifdef DEBUG
	ANVIL_FLAGS += -verbose
endif

ifdef NOOPT
	ANVIL_FLAGS += -O 0
endif

ifdef SESSIONOFF
	ANVIL_FLAGS += -disable-session-checks
endif

$(MODULE_NAME).anvil.sv: $(MODULE_NAME).anvil
ifdef LOG
	dune exec anvil $(ANVIL_FLAGS) $< > $@ 2> compile.log
else
	anvil $(ANVIL_FLAGS) $< > $@
endif

ifdef DEBUG
	python3 debug.py
endif

obj_dir/V$(MODULE_NAME): $(MODULE_NAME)_driver.cpp $(MODULE_NAME).anvil.sv
ifdef LOG
	verilator --cc --exe --build $(VERILATOR_FLAGS) $^ > /dev/null 2>&1
else
	verilator --cc --exe --build $(VERILATOR_FLAGS) $^
endif

$(MODULE_NAME)_driver.cpp: $(TEST_DRIVER)
	sed "s/Vtop/V$(MODULE_NAME)/g" $< > $@

run: obj_dir/V$(MODULE_NAME)
	@ $< $(TIMEOUT)

clean:
	rm -rf *.anvil.sv *_driver.cpp *.png *.dot *.log obj_dir