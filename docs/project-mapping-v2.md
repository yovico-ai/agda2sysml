# Project mapping version 2

Version 2 extends version 1 for parameterized specifications without changing
input Agda source. All version-1 validation rules apply unless replaced below.
The reader retains version 1 with its original meaning.

`mapping-version` is `2`. `project.inventory` is optional and is either `roots`
(the default import closure) or `library` (every source module in the declared
library's include directories). Dependency libraries are inventoried through
imports rather than recursively scanning their unrelated modules. Library-wide
inventory checks each discovered module and never executes it.

`state` may be `{infer: true}` instead of `{type: NAME}`. For function models,
the selected before-state binder supplies the type. For relation models, both
selected indices must agree. Inferred types retain their complete telescope,
implicit arguments, universe levels, and dependencies. They need not have a
closed global name. Exactly one of `infer` and `type` is allowed.

Module parameters and other context remain universally quantified inputs. The
mapping cannot instantiate a parameter with an expression or supply a default
state. The checked module telescope determines their order and types.
Function-valued module parameters proven unused by the dependency analysis may
be omitted from native calculation inputs; their source quantification remains
in the checked inventory. See [translation rules](translation-rules.md#unused-higher-order-module-parameters).

Function models may omit `commands` and `arguments.command` together. Such a
model exposes its transition function as an operation; additional arguments
remain explicit context. If commands are supplied, version-1 rules apply.

`transition.result` is either the version-1 result-family declaration or exactly
`{state: return}`. The latter requires the function's result to have the selected
state type and interprets the complete result as the after-state. It does not
invent success or refusal constructors.

An invariant selection may remain a version-1 name, or be a mapping with exactly
`symbol` and `state-argument`. The selector follows function-argument selection
rules. Other arguments remain quantified context. A selected predicate cannot
be advertised as universally established without a corresponding checked law.

The complete inventory distinguishes requirements for structure, executable
behavior, statement preservation, proof-source retention, and external
assumptions. Textual retention satisfies only the corresponding textual
requirement. It cannot satisfy an executable-behavior requirement or conceal an
unsupported dependency. Every selected model and its semantic dependency
closure is required in strict generation.

No change adds expressions, scripts, guard overrides, effect overrides, or
project-specific executable adapters to configuration.
