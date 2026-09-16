<!--
Part of the Carbon Language project, under the Apache License v2.0 with LLVM
Exceptions. See /LICENSE for license information.
SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
-->

# Site inventory for the `TypeType` to empty `FacetType` migration

This is a survey of code that branches on `FacetType` or `TypeType`, taken
before the migration began. Line numbers are approximate and will rot. Re-run
the searches rather than trusting this list to be complete:

```bash
grep -rn -E 'Is<(SemIR::)?FacetType|TryAs<(SemIR::)?FacetType|As<(SemIR::)?FacetType|InstKind::FacetType|CARBON_KIND\((SemIR::)?FacetType|IsFacetType' toolchain/
grep -rn -E 'TypeType' toolchain/
```

Classification used below:

-   **Collapses**: two branches that can merge into one.
-   **OK**: the facet path already behaves correctly for an empty facet.
-   **Guard**: the site means "constrained facet type" and should say so with
    `types().IsConstrainedFacetType(type_id)`, or with an explicit
    `!= SemIR::TypeType::TypeInstId` test if it holds an inst id.
-   **Rethink**: the site used a facet test as a proxy for something else; the
    expression no longer means what it used to.
-   **Mechanical**: a rename, since both `SemIR::TypeType::TypeId` and
    `SemIR::TypeType::TypeInstId` keep working.

## `toolchain/sem_ir/`

| Site | What it does | Class |
| --- | --- | --- |
| `type.h` ~L255 `IsFacetType` | `type_id == TypeType::TypeId \|\| Is<FacetType>(type_id)` | Collapses to plain `Is<FacetType>`; delete it and convert the 9 callers. Add `IsConstrainedFacetType` in its place |
| `type.h` ~L262 `IsFacetTypeOrError` | same plus `ErrorInst` | Keep, but implement on `Is<FacetType>` |
| `type.cpp` ~L17 `CheckTypeOfConstantIsTypeType` | a constant is a type iff its type is `TypeType` | Mechanical; the invariant is unchanged, provided empty `FacetValue`s collapse |
| `type.cpp` ~L44 `TryGetTypeIdForTypeConstantId` | "is this constant a type?" | Mechanical; returns a `TypeId` for exactly the same constants as before |
| `inst.h` ~L191 `MakeSingleton` | forces both args to `NoneIndex` | No change. Its comment about "the self-referential TypeType" stays true: it still _uses_ `TypeType::TypeId` |
| `inst.cpp` ~L118 `LocIdAndInst::RuntimeVerified` | `CHECK`s no singleton-kind inst has an import loc | No change, so long as `FacetType` does not become a singleton kind. See Hazard 2 |
| `file.cpp` ~L84 | `SetComplete(TypeType::TypeId, ...)` then builds singletons | Keep the `SetComplete`; add the `constants_.GetOrAdd` seeding before the singleton loop |
| `file.cpp` ~L69 | `insts_(this, SingletonInstKinds.size() + 1)` | Becomes `insts_(this, NumFixedInsts)` |
| `constant.cpp` ~L12 `ConstantStore::GetOrAdd` | keys dedup on `Inst` value | Create the empty facet type through it; no new entry point needed |
| `singleton_insts.h` ~L15 | `SingletonInstKinds`, positional ids | `TypeType` leaves the array entirely and takes a fixed index ahead of it; all index arithmetic gains the `NumInstsBeforeSingletons` offset |
| `ids.cpp` ~L241 | prints `type(TypeType)` | `TypeId::Print` needs no change. `InstId::Print` should gain `inst(TypeType)` / `inst(Package)` labels, and `DeclaredFacetTypeId::Print` a `declared_facet_type(Empty)` label |
| `inst_fingerprinter.cpp` ~L782 | skips self-referential `TypeType::TypeId` | No change needed; the test is `!= TypeType::TypeId`, which follows wherever it points |
| `mangler.cpp` ~L118 | `case TypeType::Kind:` mangles `ir_name` | Needs a `FacetType` case that emits `"type"` for `TypeType::TypeInstId` and otherwise calls `MangleFingerprint` |
| `type_iterator.cpp` ~L29 | `case CARBON_KIND(FacetType)` pushes constraints | OK; empty pushes nothing |
| `type_iterator.cpp` ~L137, ~L149 | `FacetType::Kind` and `TypeType::Kind` both to `ConcreteType` | Collapses |
| `type_iterator.h` ~L43, L60, L88, L176 | work-list variant and comments | Collapses; update comments |
| `inst_namer.cpp` ~L257 `GetNameFor` | singletons print `kind().ir_name()` | Add one case returning a bare `type` for `TypeType::TypeInstId`, alongside `package` for `Namespace::PackageInstId` |
| `inst_namer.cpp` ~L245 `GetUnscopedNameFor`, ~L690, ~L748 | other `IsSingletonInstId` lookups | **No change.** The inst is named by the ordinary naming pass, so special cases here are dead code |
| `inst_namer.cpp` ~L543 `PushBlockInsts` | skips singletons when naming | No change; `TypeType` now passes the filter and gets named, which is what makes the above work |
| `inst_namer.cpp` ~L1089 | names `FacetType` insts, empty to `type`/`type_where` | No change; the empty-constraints branch here is exactly what gives the fixed inst the name `type` |
| `inst_namer.cpp` ~L1115 | names `FacetValue`s incl. `HasNoConstraints()` | OK |
| `stringify.cpp` ~L303 | generic singleton overload prints `ir_name` | Verify the `FacetType` overload still wins |
| `stringify.cpp` ~L739, ~L796 | empty facet already prints `type` | OK, diagnostics unchanged |
| `stringify.cpp` ~L897 | synthesizes `ClassType{TypeType::TypeId, ...}` | Mechanical |
| `formatter.cpp` ~L1571 | `FormatArg(DeclaredFacetTypeId)` prints `<type>` | OK |
| `builtin_function_kind.cpp` ~L239 | `BuiltinType<TypeType::TypeInstId>` | Mechanical |

## `toolchain/check/` — facet-value-versus-type-value confusion

These use `types().Is<FacetType>(type_of_x)` to mean "x is a facet value". That
is exactly the class that breaks. Sites that instead compare against
`TypeType::TypeId` keep their meaning and are listed at the end of the table for
contrast.

> [!WARNING] Most of these sites really do mean "constrained facet type", for
> which `IsConstrainedFacetType` is right. `member_access.cpp` ~L609 is the
> exception that means "not a concrete type", and needs `InstIsType` instead.
> Read Hazard 6 in the SKILL before deciding.

| Site | What it does | Class |
| --- | --- | --- |
| `type_completion.cpp` ~L952 `GetSelfFacetValue` | returns as-is if facet, else wraps | No-op; every path returns the input, so delete the function and pass the constant through |
| `custom_witness.cpp` ~L33 `GetFacetAsType` | builds `FacetAccessType` if facet | Guard; a value of type `type` is already a type |
| `custom_witness.cpp` ~L248 | `Is<FacetType>(inst.type_id())` | Guard |
| `custom_witness.cpp` ~L360 | `case SemIR::TypeType::Kind:` in the trivially-destructible list | Collapses into the `FacetType` case |
| `convert.cpp` ~L1577 | facet target versus `type` target after tuple conversion | Guard |
| `convert.cpp` ~L1590 | facet value to `type` via `FacetAccessType` | Guard on both source and target |
| `convert.cpp` ~L1600 | `IsOneOf<TypeType, FacetType>` then impl lookup, builds `FacetValue` | Collapses to `Is<FacetType>` plus a `!= TypeType::TypeId` guard on the target |
| `convert.cpp` ~L1745 | diagnostic plus `BoolAsSelect` arg `== TypeType::TypeId` | Collapses; the `target.type_id == TypeType::TypeId ||` disjunct becomes redundant |
| `convert.cpp` ~L1198, ~L1206 | picks "facet to facet" versus "type to facet" wording | Guard; accepted behavior change 4 |
| `check/type.cpp` ~L307 `TryGetCanonicalFacetValue` | `type_id() != TypeType::TypeId` means not a type value | Mechanical; still exactly right |
| `cpp/generate_ast.cpp` ~L205 | `target_inst.type_id() == TypeType::TypeId` means it's a type | Mechanical; still exactly right |
| `name_lookup.cpp` ~L329 | `type_of_canonical == TypeType::TypeId` wraps type as facet | No-op; the branch returns its own input, so it and the surrounding ~20 lines collapse to `return GetCanonicalFacetOrTypeValue(...)` |

## `toolchain/check/` — lookup, impls, and `where`

| Site | What it does | Class |
| --- | --- | --- |
| `name_lookup.cpp` ~L311 | `InstIs<FacetType>` uses abstract `Self` | Guard; now true for literal `type` |
| `name_lookup.cpp` ~L382 | facet type as a lookup scope | Accepted behavior change 1 |
| `member_access.cpp` ~L531 | base is a constant facet, look up in the facet type | Guard with `!= TypeType::TypeId`; a constant of type `type` is handled by the name-scope branch above |
| `member_access.cpp` ~L609 | look up in the facet type of the base's type | **Rethink, not Guard.** `!= TypeType::TypeId` wrongly excludes an unconstrained `.Self`; use `kind().is_type() != InstIsType::Always` instead. See Hazard 6 |
| `member_access.cpp` ~L156 `ScopeNeedsImplLookup` | `Is<FacetType>` means no impl lookup | Guard with `inst_id != TypeType::TypeInstId`. **Reachable for `type`**, contrary to first impressions: `(type as Core.DefaultOrUnformed).Op()` needs impl lookup |
| `impl_lookup.cpp` ~L335 | `if (type_id != TypeType::TypeId)` then identify | Guard; the condition already reads correctly, but confirm it still excludes the singleton and watch the recursion guard |
| `impl_lookup.cpp` ~L420, ~L477, ~L986, ~L1154 | `GetAs<FacetType>` / `IsFacetType` on the query | OK, relaxes |
| `impl.cpp` ~L1005 `CheckConstraintIsFacetType` | rejects `impl X as <non-facet>` | Accepted behavior change 3 |
| `impl.cpp` ~L405, ~L791, ~L914, ~L972 | facet constraints on impls | Mechanical / OK |
| `handle_where.cpp` ~L36 `GetPeriodSelfType` | `TryGetAs<FacetType>` else `== TypeType::TypeId` | Collapses; poster child. The `== TypeType::TypeId` branch returning `GetEmptyFacetType()` is simply deleted |
| `handle_where.cpp` ~L64, L136, L238, L418, L439, L454, L475, L606 | `where` and `impls` handling | Collapses mostly |
| `facet_type.cpp` ~L467 `GetEmptyFacetType` | mints a fresh empty `FacetType` | Becomes `SemIR::TypeType::TypeId`, so delete it and inline that at its callers. **This is what makes an unconstrained `.Self` have type `type`**, which is the root of Hazard 6 |
| `facet_type.cpp` ~L474 `GetConstantFacetValueForType` | wraps a type value in an empty `FacetValue` | No-op; the `FacetValue` evaluates back to its argument. Delete it |
| `impl.cpp` ~L531, ~L936 | wrap `impl.self_id` for `MakeSpecificWithInnerSelf` | No-op; pass `constant_values().Get(impl.self_id)` inline |
| `facet_type.cpp` ~L520 `FindWhere` | skips `TypeType::TypeInstId`, then `!IsExtendedOnly()` | Collapses; early-out becomes redundant |
| `facet_type.cpp` ~L166 | rewrite RHS `Is<FacetType>` | Guard |
| `merge.cpp` ~L662, ~L686 | `TryAs<FacetType>` for interface redecl merging | Guard; empty won't match single-extend |
| `type_completion.cpp` ~L258 | `SemIR::TypeType` in the empty-at-runtime `BuildInfoForInst` list | Collapses into the `FacetType` entry |
| `type_completion.cpp` ~L512 | completes a `FacetType` | OK; singleton must be force-completed |
| `type_completion.cpp` ~L982, L1006, L1123, L1180, L1241 | facet identification | OK; empty yields zero required impls |
| `period_self.cpp` ~L146 `ConvertReplacement` | carries the migration TODO | Delete the TODO; `period_self_type_id == GetEmptyFacetType(context())` becomes `== SemIR::TypeType::TypeId` |
| `period_self.cpp` ~L164 | makes the replacement into a type if it's a facet | Guard; a replacement of type `type` is already a type |
| `period_self.cpp` ~L26, L87, L119, L125, L283, L384 | `.Self` CHECKs and substitution early-outs | OK / mechanical |
| `handle_binding_pattern.cpp` ~L165 | scans specific args for `where` | OK |
| `handle_binding_pattern.cpp` ~L226 | `.Self` allowed only if `Is<FacetType>` | Guard; unreachable in practice |
| `eval.cpp` ~L2460 `ArgToFacetTypeId` | `type & X` rejection | Accepted behavior change 2 |
| `eval.cpp` ~L3239 | `RequirementBaseFacetType` | OK |
| `eval.cpp` ~L3314 | `rhs_id == TypeType::TypeInstId` makes `X impls type` a no-op | Collapses |
| `eval_inst.cpp` ~L217 `FacetAccessType` | CHECK on operand | **Needs a new early return** for an operand of type `type`, or `ConvertEvalResultToConstantId` CHECK-fails. See Hazard 1 |
| `eval_inst.cpp` ~L240 `FacetValue` | constant evaluation | **Needs a new early return** to the inner `type_inst_id` when `type_id == TypeType::TypeId`. This is design decision 4 |
| `eval_inst.cpp` ~L298 | `Is<TypeType>` early-out before reading rewrites | Becomes `access_self_type_id == SemIR::TypeType::TypeId` |
| `deduce.cpp` ~L309 | `IsFacetType(param_type_id)` strips `as type` | OK |
| `handle_operator.cpp` ~L393 | diagnostic selection on `== TypeType::TypeId` | Guard |
| `handle_observe.cpp` ~L80, `handle_require.cpp` ~L75, `generic.cpp` ~L862 | facet-type CHECKs | OK, relax |
| `cpp/call.cpp` ~L34 | `IsOneOf<TypeType, FacetType, ...>` | Collapses |
| `cpp/export.cpp` ~L325 | `!= TypeType::TypeId && !Is<FacetType>` | Collapses |
| `cpp/operators.cpp` ~L587 | `TryGetAs<FacetType>` | Guard |

## `toolchain/check/import_ref.cpp`

-   Facet types during import: ~L1267, L1321, L1353, L3282, L3391, L3572,
    L3682, L4641, L5200. Mostly OK.
-   The `IsSingletonInstId` shortcuts at ~L4572 and ~L4981 do **not** apply to
    the empty facet type, since it is not a singleton. It takes the ordinary
    constant resolution path instead, which lands on the local canonical inst
    through `GetOrAdd`. That is the desired cross-file deduplication; the
    shortcut is an optimization, not the mechanism.
-   Roughly 18 `CARBON_CHECK(inst.type_id == SemIR::TypeType::TypeId)` calls
    (~L1737, 1840, 2185, 2239, 2381, 2803, 2825, 2841, 2858, 2875, 3878, 4082,
    4161, 4175, 4314, 4409, 4449): mechanical.

## `toolchain/lower/`

| Site | What it does | Class |
| --- | --- | --- |
| `lower/type.cpp` ~L805 | `requires(InstT::Kind.IsAnyOf<FacetType, TypeType>())`, both lower to `GetTypeType()` | Collapses; lowering is already unified |
| `lower/context.h` ~L83, ~L93, `file_context.h` ~L164 | `GetTypeType()` LLVM empty struct | Naming only |

No `FacetType` references in `toolchain/language_server/`.

## Bulk mechanical sites

Roughly 60 `.type_id = SemIR::TypeType::TypeId` initializers across `check/`
(`handle_class`, `handle_struct`, `handle_choice`, `handle_array`,
`handle_operator`, `handle_named_constraint`, `handle_impl`, `call.cpp`,
`eval.cpp`, `impl.cpp`, `facet_type.cpp`, `period_self.cpp`, `import_ref.cpp`),
plus `GetTypeImpl` in `check/type.cpp` ~L103 which stamps `TypeType::TypeId`
onto every type inst. Keeping the name `SemIR::TypeType::TypeId` pointed at the
new singleton is what keeps this from being an enormous diff.

`check/literal.cpp` ~L32 is where the surface syntax `type` maps to the
singleton, via `MakeTypeLiteral(..., TypeType::TypeInstId)`.

## Tests to expect churn in

-   Roughly 240 testdata files change. Every file with a `constants { ... }`
    block gains a leading `type: type = facet_type <type> [concrete]` line, and
    about 150 files under `toolchain/check/testdata/` already contain
    `facet_type <type>`. Concentrations: `facet/`, `where_expr/`, `interface/`,
    `named_constraint/`, `generic/`, `deduce/`, `interop/cpp/`.
-   Behavioral, not mechanical. These are split-file tests, so the containing
    file is not named after the failing case:
    -   `check/testdata/interface/fail_lookup_in_type_type.carbon`,
        `check/testdata/facet/runtime_value.carbon`
        (`fail_member_access_runtime_type`), and
        `check/testdata/facet/aggregate_through_access.carbon`
        (`fail_todo_struct_access_through_witness`) for accepted change 1.
    -   `check/testdata/named_constraint/import_type_and.carbon` for accepted
        change 2.
    -   `check/testdata/impl/fail_impl_bad_interface.carbon`
        (`fail_impl_as_type`) for accepted change 3.
    -   `check/testdata/facet/period_self.carbon` and
        `check/testdata/facet/validate_impl_constraints.carbon` for accepted
        change 4.
-   `toolchain/driver/testdata/stdin.carbon` is golden `--dump-raw-sem-ir`
    output. It gains the `TypeType` inst and the `declared_facet_type(Empty)`
    entry, and its ids change spelling to `inst(TypeType)` / `inst(Package)`,
    but the indices themselves do not shift.
-   `toolchain/sem_ir/yaml_test.cpp` is hand-written and needs three edits:
    `declared_facet_types: SizeIs(0)` becomes 1, and both the `inst_id` and
    `constant_id` regexes must accept the `inst(Name)` spelling. The
    `constant_id` one is easy to overlook. `Pair("type", "type(TypeType)")`
    does not change.
-   `toolchain/lower/testdata` **is** affected, contrary to what you might
    expect from lowering treating the two identically: the five
    `function/generic/call*.carbon` tests change because mangled names embed
    specific-argument fingerprints, and the fingerprint of the argument `type`
    changes with its inst kind.

## Pre-existing TODOs to remove

-   `check/facet_type.h` ~L61: "We vaguely plan to replace TypeType with this
    FacetType in the future, though that's a big change."
-   `check/period_self.cpp` ~L150: "TODO: Replace all empty facet types with
    TypeType." Note this points the opposite direction from the migration and
    should be deleted, not satisfied.
-   Supporting comments worth updating: `sem_ir/declared_facet_type.h` ~L124,
    `sem_ir/file.cpp` ~L85, `sem_ir/type_iterator.h` ~L176,
    `toolchain/docs/check/README.md` ~L126.
