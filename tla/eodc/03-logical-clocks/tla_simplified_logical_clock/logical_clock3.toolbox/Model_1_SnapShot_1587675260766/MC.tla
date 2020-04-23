---- MODULE MC ----
EXTENDS logical_clock3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A_p1, A_p2
----

\* MV CONSTANT definitions Proc
const_15876752188636000 == 
{A_p1, A_p2}
----

\* CONSTANT definitions @modelParameterConstants:1MaxClockValue
const_15876752188637000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2MaxInboxLength
const_15876752188648000 == 
1
----

\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_15876752188649000 ==
ActionConstraints
----
=============================================================================
\* Modification History
\* Created Thu Apr 23 13:53:38 PDT 2020 by todd
