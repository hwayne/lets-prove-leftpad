/**
 * This is the module that encapsulates the leftpad logic. A user of this module can communicate
 * with it using the following definition of the interface in order to pass the arguments and
 * obtain the result.
 * Because we are describing behaviour of a discrete-time process rather than an abstract function,
 * we need to specify when exactly our module receives the arguments and produces the output.
 * There are multiple design options, but here we opt to receive the input arguments during
 * multiple cycles, and produce the result during multiple cycles. We will, in particular, buffer
 * the input string over multiple cycles character-by-character in order to reduce the required
 * bandwidth.
 */

module leftpad
     /* We have two constant parameters that must be fixed at synthesis time */
    #(parameter STR_LEN_MAX = 8, /* Maximum accepted and produced string length */
        CHAR_W = 8) /* Width of character in bits */
                (input clk, /* Clock signal: all the events in the system will happen synchronously
                                to it. */
                    rst,    /* Reset signal used to initialise the memory */
                [$clog2(2*STR_LEN_MAX)-1:0] desired, /* Desired result length */
                [CHAR_W-1:0] cin, /* Character of the input string */
                [CHAR_W-1:0] cpad, /* Character to be used for padding */
                [$clog2(STR_LEN_MAX)-1:0] strlen, /* Input string length */
                output logic [CHAR_W-1:0] cout, /* Resulting string character */
                output logic out_en); /* Indicates whether it's OK to read cout at this clk cycle */

/**
 * Note that in the above definition the values of the input signals are unconstrained.
 * We will use the following buffered values in order to address that:
 */

logic [$clog2(STR_LEN_MAX)-1:0] strlen_la;
logic [$clog2(2*STR_LEN_MAX)-1:0] desired_la;
logic [CHAR_W-1:0] cpad_la;

/**
 * From now on, we will omit the _la suffix in the commentary for brevity.
 */

/**
 * The usage of STR_LEN_MAX contrasts with the abstract leftpad function, where input and output
 * string length may be infinite.
 */

/* This array will hold the contents of the input string */
logic [STR_LEN_MAX-1:0][CHAR_W-1:0] str;

/* For convenience, we explicitly determine how many prefix characters we have to produce */
logic [$clog2(2*STR_LEN_MAX)-1:0] padlen;

/**
 * These values help us advance the state of string input, output or padding.
 */
logic [$clog2(STR_LEN_MAX)-1:0] stridx;
logic [$clog2(2*STR_LEN_MAX)-1:0] padidx;

/**
 * We define the following states of the system:
 */
enum logic [1:0] {
    ST_READ, /* Reading the arguments */
    ST_PAD, /* Outputting padding prefix */
    ST_O_STR, /* Outputting string */
    ST_DIS /* Output disabled */
} state;

/* Output should only be read by external observers if we are outputting the prefix or the string */
assign out_en = state == ST_PAD || state == ST_O_STR;

/* We have to output min(0, desired - strlen) prefix characters */
assign padlen = strlen_la < desired_la ? desired_la - strlen_la : '0;

/**
 * We will now define the actual timing of the system and specify the state update logic.
 * The timing will determine the amount and order of output characters.
 *
 * Range of clock cycles: event
 * -1 (reset): Buffer strlen, padlen, cpad
 * [0, max(strlen - 1, 0)]: input strlen chars via cin (ST_READ)
 * [max(strlen, 1), max(strlen+padlen-1, 0)]: output cpad padlen times for padlen > 0, else skip this
 *     (ST_PAD)
 * [max(strlen+padlen, 1), max(strlen+padlen+strlen-1, 0)]: output str; skip if strlen = 0
 *     (ST_O_STR)
 */

/* Execute the statements in this block at rising edge of clk */
always_ff @(posedge clk) begin
    /* -1st cycle */
    if (rst) begin
        /**
         * Just buffer the input signals to their _la counterparts.
         * As we use the non-blocking assignment operator <=, the updated values will become
         * visible at the next clock cycle.
         */
        state <= ST_READ;
        strlen_la <= strlen;
        desired_la <= desired;
        cpad_la <= cpad;
        stridx <= '0;
        padidx <= '0;
    end else begin
        /* [0, max(strlen - 1, 0)] cycles */
        if (state == ST_READ) begin
            /* Buffer the input character */
            if (strlen_la > '0) begin
                str[stridx] <= cin;
                stridx <= stridx + 1'b1;
            end

            /* max(0, strlen - 1) cycle */
            if (stridx + 1'b1 >= strlen_la) begin
                /* If we are done buffering, reset stridx to 0 as we will reuse it for output */
                stridx <= '0;

                /* If we shouldn't produce any characters, go to ST_DIS directly */
                if (padlen > '0)
                    state <= ST_PAD;
                else if (strlen_la > '0)
                    state <= ST_O_STR;
                else
                    state <= ST_DIS;
            end
        /* [max(strlen, 1), max(strlen + padlen - 1, 0)] cycles */
        end else if (state == ST_PAD) begin
            padidx <= padidx + 1'b1;

            /* max(strlen + padlen - 1, 0) cycle */
            if (padidx + 1'b1 == padlen)
                state <= strlen_la > '0 ? ST_O_STR : ST_DIS; /* Similarly, stop for empty input */
        end
        /* [max(strlen + padlen, 1), max(strlen+padlen+strlen-1, 0)] cycles */
        else if (state == ST_O_STR) begin
            stridx <= stridx + 1'b1;

            /* If we are done outputting the string */
            if (stridx + 1'b1 == strlen_la)
                state <= ST_DIS;
        end
    end
end

/**
 * Produce the corresponding padding or string character if needed, otherwise let the output
 * character be indeterminate.
 */
always_comb begin
    case (state)
        ST_PAD:
            cout = cpad_la;
        ST_O_STR:
            cout = str[stridx];
        default:
            cout = 'x;
    endcase
end

/**
 * This concludes the design of the system. We will now proceed to formally prove it correct.
 */

/**
 * Recall our specification of the timing. Note how every cycle range in the specification
 * corresponds to the amount of characters to be read or produced. By observing how many cycles are
 * spent in each state, and that the states are ordered, we may conclude that the behaviour indeed
 * satisfies the specification of leftpad.
 * Note that our verification ignores the order of characters output during ST_O_STR: we have to
 * assume it is correct, as it cannot be expressed in LTL.
 *
 * At most 3*STR_LEN_MAX+1 cycles are relevant for us: the first cycle is spent in ST_READ, then
 * at most STR_LEN_MAX are spent in ST_READ, ST_PAD or ST_O_STR.
 */
logic [$clog2(3*STR_LEN_MAX+1)-1:0] cycle;

always_ff @(posedge clk) begin
    if (rst) begin
        cycle <= '0;
    end else if (cycle < 3*STR_LEN_MAX) /* Prevent it from wrapping */
        cycle <= cycle + 1'b1;
end

`define MAX(a, b) (a > b ? a : b)

/* Once we have transitioned from ST_READ, we never enter it again */
assert property (@(posedge clk)
    disable iff (rst) /* Nothing is initialised until the reset completes, so ignore this cycle */
    state != ST_READ |-> always (state != ST_READ));

/* We are in ST_READ state during [0, strlen-1] cycles for non-empty strings */
assert property (@(posedge clk)
    disable iff (rst)
    cycle >= '0 && strlen_la > '0 && cycle <= strlen_la - 1'b1 |-> state == ST_READ);

/* For empty strings, we are in ST_READ during cycle 0 */
assert property (@(posedge clk)
    disable iff (rst)
    cycle == '0 && strlen_la == '0 |-> state == ST_READ);

/**
 * We are in ST_PAD state during [strlen, strlen + padlen - 1] cycles for non-zero pad length.
 * If strlen_la == 0, we expect to be in ST_PAD at least since the 1st cycle.
 */
assert property (@(posedge clk)
    disable iff (rst)
    padlen > '0 && cycle >= `MAX(strlen_la, 1'b1) && cycle <= strlen_la + padlen - 1'b1
    |-> state == ST_PAD);

/* For zero pad length, we never enter ST_PAD */
assert property (@(posedge clk)
    disable iff (rst)
    padlen == '0 |-> always (state != ST_PAD));

/* If we are in ST_PAD state, we output cpad_la */
assert property (@(posedge clk)
    disable iff (rst)
    state == ST_PAD |-> cout == cpad_la);

/* ST_PAD always precedes ST_O_STR, i.e. may never succeed ST_O_STR */
assert property (@(posedge clk)
    disable iff (rst)
    state == ST_O_STR |-> always (state != ST_PAD));

/**
 * As we have established above that ST_PAD always precedes ST_O_STR, and we always output cpad_la
 * when in ST_PAD, we conclude that the prefix of the output is padding characters and nothing but
 * padding characters.
 */

/**
 * We are in ST_O_STR state during [strlen+padlen, strlen+padlen+strlen - 1] cycles for strlen > 0
 * For empty strings it does not matter whether we ever enter ST_O_STR state.
 */
assert property (@(posedge clk)
    disable iff (rst)
    strlen_la > '0 && cycle >= strlen_la + padlen &&
    cycle <= strlen_la + padlen + strlen_la - 1'b1
    |-> state == ST_O_STR);

/* During [strlen+padlen, strlen+padlen+strlen - 1] cycles for non-empty string, we output str[cycle - strlen - padlen] character */
assert property (@(posedge clk)
    disable iff (rst)
    strlen_la > '0 && cycle >= strlen_la + padlen &&
    cycle <= strlen_la + padlen + strlen_la - 1'b1
    |-> cout == str[cycle - strlen_la - padlen]);

/**
 * Length of the output is max(strlen_la, desired_la).
 */
assert property (@(posedge clk)
    disable iff (rst)
    (desired_la < strlen_la ?
        (`MAX(strlen_la, 1'b1) <= cycle && cycle <= `MAX(strlen_la, 1'b1) + strlen_la - 1'b1) :
        (`MAX(strlen_la, 1'b1) <= cycle && cycle <= `MAX(strlen_la, 1'b1) + strlen_la +
            (desired_la - strlen_la) - 1'b1)) iff
    out_en);

/**
 * Here is a few example executions expressed as SVA. Operator |=> is a right-associative
 * implication where the right hand side must hold at the next clock cycle.
 *
 * During the input cycles, we don't need to constrain the state if we are confident that the system
 * reads the input correctly.
 */

/* leftpad('!', 5, "foo") */
sequence seq_example0_in;
    cycle == 0 && strlen_la == 3 && desired_la == 5 && cpad_la == "!" &&
    /* state == ST_READ && */ cin == "f" ##1
    /* state == ST_READ && */ cin == "o" ##1
    /* state == ST_READ && */ cin == "o";
endsequence

sequence seq_example0_out;
    state == ST_PAD && cout == "!" ##1
    state == ST_PAD && cout == "!" ##1
    state == ST_O_STR && cout == "f" ##1
    state == ST_O_STR && cout == "o" ##1
    state == ST_O_STR && cout == "o" ##1
    state == ST_DIS;
endsequence

assert property (@(posedge clk)
    disable iff (rst)
    seq_example0_in |=>
    seq_example0_out);

/* leftpad('!', 0, "foo") */
sequence seq_example1_in;
    cycle == 0 && strlen_la == 3 && desired_la == 0 && cpad_la == "!" &&
    /* state == ST_READ && */ cin == "f" ##1
    /* state == ST_READ && */ cin == "o" ##1
    /* state == ST_READ && */ cin == "o";
endsequence

sequence seq_example1_out;
    state == ST_O_STR && cout == "f" ##1
    state == ST_O_STR && cout == "o" ##1
    state == ST_O_STR && cout == "o" ##1
    state == ST_DIS;
endsequence

assert property (@(posedge clk)
    disable iff (rst)
    seq_example1_in |=>
    seq_example1_out);

endmodule : leftpad
