proc fail msg {puts stderr $msg; exit 6;}
proc abort msg {puts stderr $msg; exit 7;}
set timeout 40
expect_after default {fail "Got <$expect_out(buffer)> but expected something else."}
