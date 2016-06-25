The purpose of this document is to document which design heuristics have
resulted in tolerable code, and which patterns might be indicative of a dead
end. The intent is to document experience (imperical results), not comprehensive
truth. For each guideline here, there probably exists some situation where it is
best to deviate from the said guideline. Yet incomplete wisdom is better than no
wisdom, so let's note down the trade-offs we have faced and how we have resolved
them.

# Data representations

## Validity

### Obvious validity

For some data, the obvious simple type can only take meaningful values --
a natural number is either zero or the successor of another natural number, and
that is all there is to it. This section covers the cases when the choice of
correct representation is not obvious.

### Validity by a well-engineered simple type structure

If using a representation where the type only admits semantically valid values
would not make the functions that operate that type look horrendous, use that
representation. For example, the Coq standard library represents a rational
number as a pair of a integer numerator and `positive` denominator, and it works
out okay. Fractions with 0 denominator can not be represented because there is
no value of type `positive` that would be interpreted as zero.

On the other hand, an elliptic curve point in Edwards coordinates is informally
defined as a pair `(x, y)` s.t. `x^2 + y^2 = 1 + d*x^2*y^2`. It is no longer
obvious how one would hack up a simple type that only represents valid points.
A solution that gets quite close would be to use "point compression": store `y`
and the sign bit of `x`; solve for `x` each time it is needed. Yet this
representation is not unique (there are two ways to represent a point with
`x=0`), and solving for `x` would clutter all functions that operate on `x` and
`y`. Uniqueness can still be restored at the cost of cluttering the functions
even more: one could make a type that has three cases `Xpositive`, that takes
a `y`, `Xnegative` that takes a `y`, and `Xzero` that represents the point `(0,
1)` but does not allow a superfluous y to be specified.

The alternative is to first write down a type that can represent all valid
values and some invalid ones, and then disallow the invalid ones. Sometimes
disallowing the invalid values can be circumvented by redefining validity: it
may be possible to extend an algorithm that only operates on positive numbers to
work with all natural numbers or even all integers. Sometimes the validity
condition is crucial: the group law for combining two Edwards curve points is
only proven to be associative for points that are on the curve, not for all
pairs of numbers.

### Validity using dependent types

If nontrivial data validity invariants are required, the intuitive "value such
that" definition can be encoded as a sigma type: `Definition point := { P | let
'(x,y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2 }`. In this encoding, every time
a value of type `point` is constructed out of the `x` and `y` coordinates,
a proof that the point is valid will need to be provided. Code that manipulates
point using functions that are already known to return points does not need to
deal with the invariant: a value that comes out of a function that returns
`point` is valid because wherever it was that the value was constructed from
coordinates, a validity proof must have been provided. Using sigma types this
way moves proof obligations from one place in the code to another, hopefully
more convenient place.

Dependent types are not a free lunch, we have encountered three types of issues
when dealing with them.

#### Rewriting

The `rewrite` tactic does not work in equations that construct a point from
its coordinates and a proof. This is because after rewriting just the
coordinates, the proof would still refer to the old coordinates, and thus the
construction would not be valid. It might be possible to make rewriting work by
showing an equivalence relation on values such that the invariant does not
become invalidated when replacing one equivalent value with another, and the
rewrite only changes the value within an equivalence class. It might even be
possible to hook this argument with the `setoid_rewrite` tactic to automate it.
However, a more lightweight rule has been successful enough to keep us from
pursuing that strategy: when non-trivial equational reasoning on the value is
required, it can be done separately from the invariant preservation proof. For
example, when aiming to implement an optimized `add : point -> point -> point`,
first define `add_coordinates : F*F -> F*F -> F*F` that operates on arbitrary
pairs of coordinates, do all the rewriting you want, and then define `add` in
terms of `add_coordinates`. In analogy to Java's `public` and `private`
annotations, users of the Edwards curve `point`s never operate on the
coordinates alone, while the implementation of point addition operates on
coordinates and proves invariant preservation separately.

#### Computation inside Coq

Computing values of a proof-carrying type inside Coq often runs unreasonably
long or uses unreasonably much memory. However, computing the coordinates of the
same point that itself would take too long to compute seems to work fine. In
cases were the evaluation heuristics do not manage to make this okay, rewriting
the expression before evaluating it has not been too difficult.

#### Equality and Equivalence

Equality and invariant preservation proofs do not play nice by default. Under
Leibniz equality, showing that two points with equal coordinates are equal
requires showing that the invariant preservation proofs are equal. This can be
done using the `UIP_dec` lemma if the invariant itself is an equality and that
for all values of coordinates it is decidable to compute whether the invariant
holds on them or or not. A principled way of representing an invariant `P : T ->
Prop` as an equality is to define `check_P : T -> bool` s.t. `check_P x = true
<-> P x` and use `{x | is_true (check_P x) }` as the type of valid values^[This
technique is used extensively in `ssreflect`.]. Alternatively, two points can be
defined to be equivalent (not equal) if they have the same coordinates (working
with custom equivalence relations involves nontrivial considerations of its
own).

#### Note on defining values

The most reliable way to make a value of a sigma type is to start the
`Definition` in proof mode (ending the first line with a dot like `Definition
zero : point.`) and then do `refine (exist _ value _); abstract
(tacticThatProvesInvariant)`. Another way of doing this is to first do
`Obligation Tactic := tacticThatProvesInvariant.` and then `Program Definition
zero : point := exist _ value _.` which will call the tactic to fill in the
holes that implicit argument inference does not fill. By default, `Program
Definition` rewrites all match statements using the convoy pattern, and this can
clutter definitions quite badly. Neatness of resulting definitions takes
priority over neatness of source code. To prevent `Program Definition` to
rewriting a match statement, specify an explicit return clause: `match x return
_ with ... end.`

## Equivalence

Terms can be equivalent in different ways. In this list, each kind of equality
is stricter than the one right after it.

- syntactic: they are literally the same expression. Proof automation is
sensitive to syntactic changes.
- definitional: one term can be transformed into the other by applying rules of
computation only. Proof checking considers two syntactically different
expressions interchangeable as long as they are definitionally equal.
- propositional: as established by a proof (which can use lemmas in addition to
rules of computation), these two terms would compute to the exact same vale. It
is always possible to rewrite using a propositional equality
- custom equivalence relations: for example, two fractions `a/b` and `c/d` can
be defined equivalent iff `a*d = b*c`. Given `x == y`, it is possible to rewrite
`f(g(x))` to `f(g(y))` if there is some equivalence relation `===` such that the
output of `f` does not change when one `===`-equivalent thing is replaced with
another, and the output of `g` only changes within a `===`-equivalence class
when the input changes within a `==`-equivalence class. This is what `Proper`
instances are about; the last statement can be written `Proper((==)=>(===))g`.

### Which equivalence to use?

When defining a datatype from scratch, try to define it in a way that makes
propositional equality coincide with the desired notion of equivalence. However,
as with sigma types, it is not worth garbling the code itself to use the
propositional equality

When defining a datatype that has a field of a type that is used with a custom
equivalence, it is probably a good idea to define the obvious custom equivalence
relation for the new type right away (and make and `Equivalence` instance for
the relation and `Proper` instances for constructors and projections. When
defining a type parametrized over some other type, and it is likely that some
use of the parametric type will be set the parameter to a type with a custom
equivalence relation, define an equivalence relation for the new type,
parametrized over an equivalence relation for the parameter type.

When writing a module that is parametric over a type, require the weakest
sufficient equivalence. In particular, if there is a chance that the module will
be instantiated with a type whose propositional equivalence makes little sense,
it is well worth requiring additional parameters for `Proper` and `Equivalence`
(and maybe `Decidable`) instances. See the Algebra library for an example.

When writing a tactic, specify on the form of the input goal format with
syntactic precision -- trying to be insensitive to syntactic changes and only
require definitional equality can lead to arbitrary amounts of computation and
is usually not worth it. One possible exception is the
reification-by-typeclasses pattern which has not yet had issues even when it
works up to definitional equivalence to the extent typeclass resolution does.

### Custom Equivalence Relations and Tactics

The primary reason for avoiding custom equivalence relations is that the tactic
support for them is incomplete and sometimes brittle. This does not mean that
custom equivalence relations are useless: battling with a buggy tactic can be
bad; reformulating a proof to bypass using custom equivalence relations is often
worse. Here are some suggestions.

1. The number one reason for hitting issues with custom equivalence relations is
that either the goal or the givens contain a typo that switched one equivalence
relation with another. In particular, `<>` refers to negation of propositional
quality by default. This can be avoided with good conventions: when introducing
a type that will be used with a custom equivalence relation, introduce the
equivalence relation (and its `Equivalence` instance) right away. When
introducing a function involving a such type, introduce a `Proper` instance
right away. Define local notations for the equivalences used in the file. Note
that while introducing the tooling may clutters the source code, section
parameters introduced using `Context {x:type}` are required for the definitions
in the section only if the definition actually refers to them.
2. Use normal `rewrite` by default -- it can deal with custom equivalence
relations and `Proper` instances.
3. To rewrite under a binder (e.g. `E` in `Let_In x (fun x => E)` or `E` in `map
(fun x => E) xs`) use `setoid_rewrite`. However, `setoid_rewrite` tries to be
oblivious to definitional equality -- and in doing so, it sometimes goes on
a wild goose chase trying to unfold definitions to find something that can be
rewritten deep down in the structure. This can cause arbitrary slowdowns and
unexpected behavior. To dodge the issues, mark the definitions as `Local Opaque`
before the `setoid_rewrite` and re-set to `Local Transparent` after.
4. When a `rewrite` fails (probably with an inexplicable error message),
double-check that the conventions from (1) are followed correctly. If this does
not reveal the issue, try `setoid_rewrite` instead for troubleshooting (it
sometimes even gives sensible error messages in Coq 8.5) but revert to `rewrite`
once the issue has been found and fixed. If rewriting picks the wrong
`Equivalence` or `Proper` instance for some type or function (or fails to find
one altogether), troubleshoot that separately: check that `pose (_:@Equivalence
T equiv)` or `pose(_:Proper (equiv1==>equiv2) f)` give the right answer, and if
not, `Set Typeclasses Debug` and read the log (which is in the hidden `*coq*`
buffer in `proofgeneral`). A useful heuristic for reading that log is to look
for the first place where the resolution backtracks and then read backwards from
there.
5. To perform multiple rewrites at once, make rewrite hint database and call
`(rewrite_strat topdown hints dbname).` where `topdown` can be replaced
with `bottomup` for different behavior. This does not seem to unfold
definitions, so it may be a reasonable alternative to using `Local Opaque` to
protect definitions from `setoid_rewrite`.

# Generality and Abstraction

Coq has ample facilities for abstraction and generality. The main issue we have
faced is that undisciplined use of them can clutter definitions even when only
the properties of the definitions are to be abstracted. We are not sure that the
strategy we are currently working with is optimal (in particular, it results in
verbose code), but it definitely dodges some issues other approaches do not. In
particular, we want to relate a specific set of types and operations to an
abstract structure (e.g., a group) without changing the definitions of any of
the type or operations involved. This reduces the interlock between concrete
definitions and abstractions and also enables relating the same definitions to
an abstract structure in multiple ways (e.g., integers can be a semiring under
`+` and `*` or under `max` and `+`). Furthermore, we require that it be possible
to manipulate abstractions using tactics.

To define an abstraction, fist open a module with no parameters to make a new
namespace for the abstraction (even if the entire file is dedicated to one
abstraction). Then open a new section and add to the context parameters for all
definitions. The requirements which need to be satisfied by the definitions to
fit the structure can be defined using a typeclass record. When a one of the
requirements is a typeclass, mark the field name as a `Global Existing Instance`
right after declaring the new record. To prove lemmas about everything of that
structure, introduce an instance of that typeclass to the context (in additions
to the parameters). To relate a specific set of definitions to an abstract
structure, create a `Global Instance` of the parametric typeclass for that
structure, with the specific definitions filled in. To use a lemma proven about
an abstract structure in a specific context, just apply or rewrite using it --
typeclass resolution will most likely determine that the specific definitions
indeed fit the structure. If not, specify the parameters to lemma manually (a
definitive description of what parameters are required and in what form can be
seen using `About lemma_name.`).

Compared to other means of abstraction, this one does not create common notation
for all instances of the same structure. We define notations for each specific
definition, and separate them using notation scopes (which are often named after
datatypes). It would be possible to add a typeclass field that aliases the
specific definition and define a global notation for it, but definitions that
use that notation would then gain an extra layer of definitions: each underlying
operator would be wrapped in the abstract one for which the notation was
defined. Furthermore, this interferes with having one definition satisfy the
same structure in multiple ways.

Another alternative is to use the Coq module system (which can be understood by
reading the documentation of the Ocaml module system documentation), and when
applicable, this is usually a good idea. When parameters are set once and used
very many times, the module system can be quite convenient. However, if the
number of parameters and the number of places where the values of them are
determined are comparable to the number of uses of abstractly proven lemmas, the
module system can be cumbersome. Modules cannot be instantiated automatically.
