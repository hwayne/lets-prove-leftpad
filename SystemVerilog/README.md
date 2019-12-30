# About SystemVerilog

SystemVerilog is a language for design, specification and verification of hardware behaviour.
It allows for specification of discrete-time signal-driven processess that may drive signals
continuously, or periodically update values in memory based on designer-specified logic. A model
written in SystemVerilog is said to be _synthesizable_ if it can be physically realised in
[FPGA](https://en.wikipedia.org/wiki/Field-programmable_gate_array) or by
[VLSI](https://en.wikipedia.org/wiki/Very_Large_Scale_Integration) process after translation
into equivalent logical primitives. A non-synthesizable design may still be used e.g. for
simulation. In this submission, we focus on a synthesizable model of leftpad and its formal
verification.

SystemVerilog supports verification of formal properties expressed in SystemVerilog Assertion
language (SVA), which is based on
[Linear Temporal Logic](https://en.wikipedia.org/wiki/Linear_temporal_logic). The properties can
then be verified using a model checker that supports SVA. This submission has only been tested with
Cadence JasperGold tool, but it may also be verified e.g. using
[Yosys](http://www.clifford.at/yosys/cmd_verific.html).

To verify the design, navigate to this directory in shell, and invoke `jg -fpv leftpad_jg.tcl`.
Alternatively, you may specify `leftpad` as top-level module, `clk` and `rst` as global clock and
reset signals, respectively, to an SVA model checker of your choice.

The system model, formal properties and detailed commentary can be found in file `leftpad.sv`.

SystemVerilog is an IEEE standard available at no cost at
[Accelera website](https://www.accellera.org/downloads/ieee).
