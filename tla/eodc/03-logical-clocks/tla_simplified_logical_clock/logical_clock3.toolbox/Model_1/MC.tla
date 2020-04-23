---- MODULE MC ----
EXTENDS logical_clock3, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
p1, p2
----

\* MV CONSTANT definitions Proc
const_158768250461831000 == 
{p1, p2}
----

\* CONSTANT definitions @modelParameterConstants:1MaxClockValue
const_158768250461832000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:2MaxInboxLength
const_158768250461833000 == 
2
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_158768250461834000 ==
Constraints
----
\* ACTION_CONSTRAINT definition @modelParameterActionConstraint:0
action_constr_158768250461835000 ==
ActionConstraints
----
=============================================================================
\* Modification History
\* Created Thu Apr 23 15:55:04 PDT 2020 by todd
