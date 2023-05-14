----------------------------- MODULE Regressions -----------------------------
EXTENDS TLC, Integers, Sequences, IOUtils

AbsolutePathOfTLC == 
    TLCGet("config").install

Cmd ==
    <<"bash",
    "-c",
    "java " \o
    "-XX:+UseParallelGC " \o
    "-cp %1$s tlc2.TLC " \o
    "-noTE show521677simple">>

-----------------------------------------------------------------------------

Check(wcl, rcl) ==
    IOEnvExecTemplate(
        [ WCL |-> wcl, RCL |-> rcl ], Cmd, <<AbsolutePathOfTLC>>).exitValue

ASSUME Check("strong", "strong") = 0
ASSUME Check("strong", "session") = 0 
ASSUME Check("strong", "eventual") = 13

ASSUME Check("session", "strong") = 13
ASSUME Check("session", "session") = 0
ASSUME Check("session", "eventual") = 13

ASSUME Check("eventual", "strong") = 13
ASSUME Check("eventual", "session") = 13
ASSUME Check("eventual", "eventual") = 13
=============================================================================
-------- CONFIG Regressions --------
\* TLC always expects a config file
===================================