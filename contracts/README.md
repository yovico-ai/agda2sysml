# Independent general contracts

These specifications express universally quantified transition laws. They have
no selected IDs, sample worlds, or closed regression assertions. They also serve
as independent public consumers of the generator's mapping contract.

`Guarded` abstracts over every universe level, state domain, guard, and update
operation. Its outcome is indexed by the before-state. Its laws establish that
every refused or unchanged result preserves that complete state. The mapping
retains the module parameters as context and selects the two operation inputs
by their declared binder names.

Inside the root development shell, enter this directory and run
`agda --safe Guarded.agda`. Concrete parser, serializer, and extraction checks
belong to the Haskell test suite.

`Relational` abstracts over every state domain, admissibility predicate, and
advance operation. Its indexed constructors preserve stay/move alternatives,
and its preservation theorem transfers every invariant preserved by admissible
advances to every permitted edge. The relation mapping selects both indices
after the module parameter telescope.

`Implication` specifies the logical order of Boolean guards using an indexed
relation with explicit witnesses. It proves reflexivity and transitivity for
all Boolean values. Its mapping exercises a complete native finite-relation
translation; it does not weaken the parameterized relation requirements of
`Relational`. `Contracts.agda` is the safe aggregate for these contracts.

`Register` defines a Boolean register with independently writable value and enable
fields. Its laws quantify over every state and update: writes preserve the enable
flag, enable changes preserve the value, retaining preserves the whole state,
and replacement returns the complete supplied state. Reconstruction proves the
record product law. Its mapping exercises records, nested constructor payloads,
projections, and constructor case expansion.

`RegisterWorkflow` composes two register steps through native helper calls. Its
laws quantify over all states and commands: retain is neutral on either side,
three-step sequencing reassociates, and final replacement returns the supplied
state. Its mapping exercises imported helper closure and nested positional calls.

`Parameterized` specifies generic boxes and choices, with universally quantified
identity, replacement, projection, and constructor-selection laws. Independent
Boolean and colour registers then use the same generic carriers and operations.
Their transition laws preserve the other register for every state and command.
The mapping requires distinct concrete instantiations while retaining the generic
declarations and theorems in the checked source inventory.

`UniversePolymorphic` specifies arbitrary-level boxes, lifted carriers, identity,
and enclosure with universally quantified preservation and round-trip laws.
Its register transition composes those operations at distinct closed levels.
`universe-polymorphic.yaml` exercises compiler level normalization, ordered static
arguments, nested native carriers, and projection-like calls. The integration
suite validates the generated model and evaluates projections and identity calls;
returned construction retains the documented Pilot evaluation limitation.

`Indexed` specifies phase-indexed permits and Boolean-indexed flags, together with
index-preserving operations and a phase-changing approval operation. Its general
laws quantify over every admissible payload and state. `indexed.yaml` exercises
fixed-index fields, dependent helper signatures, omitted finite indices, and
constructor refinements. Integration evaluates valid and invalid native index
constraints as well as payload observations; construction semantics also have
independent expression-algebra tests.

`DependentRecord` combines phase- and Boolean-dependent fields in one record.
Its laws cover reconstruction, projection, observations, and state transitions for
all admissible values. `dependent-record.yaml` drives native constraints for both
field dependencies and their calculation signatures. Integration checks valid
records and independent mismatches in either index, then evaluates observations
through dependent helpers. Construction and eta expansion have independent
expression-algebra coverage because of the Pilot's returned-construction limit.

`SpecializedIndexed.agda` specifies universe-polymorphic indexed families and
dependent records, with general copy, reconstruction, projection, update, and
preservation laws. `specialized-indexed.yaml` exercises concrete payloads at two
universes, Boolean and enumeration indices, omitted static/runtime arguments,
and distinct fixed fibres nested in a generic box. Native evaluation checks
field constraints, projections, and payload dispatch; the expression-algebra
tests also check construction and inconsistent-index refusals.

`DependentPayload.agda` specifies sums with ordered dependent payloads, including
Boolean/enumeration indices, proper projections from preceding record payloads,
and indexed constructor results with concrete type/universe specialization.
`dependent-payload.yaml` maps its general reconstruction, matching, and update
laws. Integration checks valid and mismatched indices, missing active slots,
inactive slots, payload dispatch, and nested matching. Independent algebraic
evaluation also checks reconstruction after both prefix and member matching.


`ComputedIndex.agda` specifies Boolean and heterogeneous finite helper chains,
computed constructor result indices, and specialized record fields indexed by a
calculation over preceding values. General laws cover observation, copying,
construction, and transitions. `computed-index.yaml` drives CLI validation and
native evaluation of admitted calculations and valid/invalid index constraints.


`Witnessed.agda` specifies a state relation whose constructors retain observational
metadata without using it in their endpoints. Its universally quantified source
and target laws cover every edge. `witnessed.yaml` exercises the real compiler
and native rule constraints, including multiple same-domain witnesses and
metadata from a different finite domain. Exhaustive binding-layout regressions
remain in the Haskell suite.
