`ifndef CLN_FUNCTIONS_INCLUDED_
`define CLN_FUNCTIONS_INCLUDED_

function automatic integer log2minimum1;
  input integer value;
  begin
    log2minimum1 = $clog2(value);
    if (log2minimum1 == 0)
      log2minimum1 = 1;
  end
endfunction

function automatic integer upperdiv;
  input integer value1, value2;
  begin
    if (value1%value2 != 0)
        upperdiv = value1/value2 + 1;
    else
        upperdiv = value1/value2;
  end
endfunction

`endif // CLN_FUNCTIONS_INCLUDED_
