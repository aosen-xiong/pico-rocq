# Semantic Immutability for Racy Derived Caches

## Abstract

Immutable objects in practical object-oriented programs are often not
syntactically immutable.  They may contain mutable fields used for lazily
computed caches, and those fields may be read and written without
synchronization.  A standard example is a String-like hash cache: the observable
value of the object is fixed, but a private cache field may change from an
unknown sentinel to a derived value.  Existing abstract immutability systems
explain why such cache fields need not belong to an object's abstract state, but
they do not by themselves justify racy cache accesses under weak memory.
Conversely, weak-memory semantics explain which writes a read may observe, but
they do not by themselves provide an object-level account of semantic
immutability.

This paper gives a generic semantic theory for racy derived caches.  The theory
is parameterized by a stable abstract-state provider, written
`StableAbs(o, a)`, which states that object or record `o` represents a fixed
abstract value `a`.  A cache protocol then assigns each excluded cache field a
validity predicate over the stable abstract value.  The key invariant is
history-based: every value ever written to an excluded cache field is either an
unknown/default value or a value derived from `a`.  Under a weak-memory-
parametric field-history interface, every cache read observes some value from
the corresponding field history.  It follows that every cache read observes
only values permitted by the cache protocol, even when different reads of the
same field observe different writes.

The main result is a derived-cache method soundness theorem.  If `StableAbs(o,
a)`, `CacheHistOK(P, o, a)`, a read-from-history memory interface, and a
trace-robust method-safety judgment `CacheSafe(m, P, F)` hold, then every
execution of `m(o, args)` returns the pure result `F(a, args)` and preserves
`SemImm(P, o, a) = StableAbs(o, a) * CacheHistOK(P, o, a)`.  The same theorem
gives a refinement result: the cached implementation refines a pure
implementation that recomputes from `a`.  PICO is one instantiation of the
stable abstract-state provider.  PICO identifies abstract-state fields and
proves abstract immutability, while the generic Iris/Rocq wrapper proves that
excluded cache mutation is semantically invisible.

The mechanized core is intentionally not a full Java Memory Model
formalization.  It assumes a field-history interface in which reads come from
histories, writes extend histories, values are not torn, cache writes are
grounded in stable abstract state, and stable abstract state is supplied by an
external invariant or proof system.  Happens-before, final-field freeze
actions, causality validation, out-of-thin-air prevention, and full Java
execution validation are outside the current mechanized core.  A future Java
Memory Model instantiation would need to prove that Java-legal executions
satisfy the field-history interface used here.

## 1. Introduction

The usual slogan for immutable objects is simple: after construction, their
state does not change.  The slogan is too simple for many production libraries.
Objects that are conceptually immutable often contain fields that are mutated
after construction for performance.  A hash code may be computed lazily and
cached.  A parsed value may retain a raw representation while caching decoded
components on demand.  A numeric object may cache the result of expensive bit
operations using sentinel encodings.  These fields are mutable, but their
mutation is intended to be unobservable: the cache is a representation device,
not part of the abstract value clients are allowed to distinguish.

This observation is not new.  Abstract immutability systems, including Javari
and later reference-immutability systems, explicitly allow selected state to be
excluded from the abstract state of an object.  PICO follows this line: it
distinguishes abstract-state fields from excluded representation state and
proves that protected abstract-state fields are not mutated.  That theorem is
important, but it does not close the full semantic gap for a common cache
pattern.  Many derived caches are accessed concurrently without synchronization.
In such code, a sequential proof that a cache update preserves an invariant is
not enough.  A racy read may see an old write, and two racy reads of the same
field in one method call need not observe the same write.  A proof of semantic
immutability must explain why these weak observations still cannot change the
abstract behavior of the object.

Weak-memory models address a different part of the problem.  The Java Memory
Model specifies which executions Java programs may have, including executions
with data races, synchronization, final fields, and causality constraints
[@manson2005jmm].  Work on promising semantics and related relaxed-memory
models studies how to rule out circular or out-of-thin-air executions while
permitting compiler and hardware reorderings [@kang2017promising].  These
semantics are about allowed executions.  They do not, by themselves, say that a
particular mutable field is semantically irrelevant to an object's abstract
state.  For derived caches, the useful theorem is object-specific: if all
values that can be read from cache fields are valid representations of the same
stable abstract value, then reading and writing those cache fields does not
change the object's abstract behavior.

This paper connects the two perspectives using a small, explicit interface.  We
do not attempt to formalize the Java Memory Model.  Instead, we isolate a
field-history property that a future Java instantiation would need to prove:
each cache read observes a whole value from the corresponding field's write
history, and each cache write extends that history.  The semantic cache theorem
is parametric in any memory model that provides this interface.  The theorem
therefore does not claim that all Java executions are modeled.  It identifies
the exact memory assumption needed by the derived-cache proof.

The central idea is to move the cache invariant from the current heap to the
field history.  In a sequential setting, it is tempting to say that the current
value of `o.hash` is either `0` or the correct hash of `o`'s stable contents.
Under weak memory, that invariant is too weak.  A read need not observe the
current value; it may observe an old value.  The invariant must instead say that
every value ever written to `o.hash` is valid for the same abstract value.  Once
the invariant is history-based, the read-from-history interface turns it into a
read guarantee: every observed cache value is valid.

History validity alone is not sufficient.  A method that reads racy cache
fields must be correct for every trace of valid observations.  This trace
robustness condition captures weak-memory effects abstractly.  In particular,
the method cannot assume that two reads of one cache field agree, and it cannot
assume that reads of multiple cache fields form one coherent global snapshot.
The proof obligation is therefore not "the cache currently contains a good
value"; it is "the method is correct for all valid cache-read traces."

A String-like hash cache illustrates the distinction.  Suppose the true hash is
`H`, with `H != 0`, and the cache protocol allows `0` as unknown and `H` as the
known value.  The implementation

```java
if (hash == 0) {
    hash = computeHash();
}
return hash;
```

is not trace robust.  The valid trace `read(hash) = H; read(hash) = 0` takes the
else branch and then returns `0`, which is not the correct result.  The usual
local-copy pattern avoids this error:

```java
int h = hash;
if (h == 0) {
    h = computeHashFromStableAbstractState();
    if (h != 0) {
        hash = h;
    }
}
return h;
```

The proof does not rely on the cache being synchronized.  It relies on two
facts: each read produces a protocol-valid value, and the method's control flow
uses a local copy rather than re-reading the racy field for the result.

This paper makes the following contributions.

1. We define a generic cache protocol over field histories.  The protocol is
   independent of Java, PICO, and any particular cache field.  It assigns each
   excluded cache field a validity predicate over a stable abstract value.

2. We introduce trace-robust cache safety.  `CacheSafe(m, P, F)` requires a
   method to return the pure result `F(a, args)` for every valid trace of cache
   observations and to write only protocol-valid cache values.

3. We prove a semantic immutability theorem.  Given stable abstract state,
   valid cache histories, a read-from-history memory interface, and a cache-safe
   method, method execution preserves `SemImm(P, o, a)` and returns the pure
   recomputation result.

4. We derive a refinement theorem.  A cached implementation refines a pure
   implementation that ignores cache state and recomputes directly from the
   stable abstract value.

5. We separate PICO from the generic cache theory.  PICO supplies
   `StableAbs(o, a)` by proving that abstract-state fields are protected and
   that excluded cache fields are outside the abstract state.  The cache theorem
   then applies to PICO and to any other system that can supply a stable
   abstract-state predicate.

6. We mechanize the core theory in Rocq and expose Iris-facing wrappers.  The
   artifact contains PICO-independent definitions of `StableAbs`,
   `CacheProtocol`, `CacheHistOK`, `ValidTrace`, and `CacheSafeMethod`; a
   generic read-from-history soundness theorem; a method-soundness theorem; a
   derived-cache instance; bad and good hash-cache traces; and staged
   Iris-facing wrappers and state-interpretation boundaries.

7. We present three case-study families as instances of the same theorem:
   String-like hash caches, URI-like decoded-component caches, and
   BigInteger-like numeric caches with sentinel encodings.

The paper is scoped deliberately.  It does not prove full Java Memory Model
soundness.  It does not verify OpenJDK.  It does not provide a production
checker for arbitrary Java cache code.  It proves a weak-memory-parametric,
field-history theorem that isolates the semantic condition under which racy
derived caches are invisible.

## 2. Motivating Examples

### 2.1 A String-Like Hash Cache

A String-like object has stable contents and a cached hash.  The abstract state
is the sequence of characters.  The cache field is not part of that abstract
state; it is a memoized result of a deterministic function `stringHash(a)`.
Ignoring the zero-hash complication for a moment, the cache protocol for a
single integer field can be written as follows:

```text
H = stringHash(a)

Valid_hash(a, h) =
    h = 0
 or (h = H and H != 0)
```

The value `0` is an unknown sentinel.  If the true hash is nonzero, a nonzero
cache value is valid only when it is the true hash.  The history invariant is
not about the last write alone:

```text
CacheHistOK(P, o, a) =
  for every cache field k governed by P,
  for every value v in history(o.k),
  Valid_k(a, v).
```

This invariant is strong enough for racy reads.  If a read of `o.hash` observes
some value from `history(o.hash)`, the value is valid for `a`.

The following implementation is tempting but wrong under the trace model:

```java
int hashCode() {
    if (hash == 0) {
        hash = computeHashFromStableAbstractState();
    }
    return hash;
}
```

For `H != 0`, the trace `read(hash) = H; read(hash) = 0` is valid.  The first
read makes the branch condition false.  The second read supplies the return
value, so the method returns `0` instead of `H`.  The method is therefore not
cache-safe.  Notice that the failure is not a violation of the cache protocol:
both `H` and `0` are individually valid observations.  The failure is a method
proof failure.  The method assumes coherence between two racy reads that the
memory interface does not provide.

The local-copy version is trace robust:

```java
int hashCode() {
    int h = hash;
    if (h == 0) {
        h = computeHashFromStableAbstractState();
        if (h != 0) {
            hash = h;
        }
    }
    return h;
}
```

If the first read returns `H`, the method returns `H`.  If it returns `0`, the
method recomputes `H` from stable abstract state and returns `H`.  The only
write is `hash = H`, and that write is valid for the same abstract value.  The
proof does not require a second read to agree with the first, because there is
no second read whose value affects the result.

### 2.2 Zero Hashes and a Second Cache Field

Real String-like hashes may be zero.  A single `0` sentinel cannot distinguish
"not yet cached" from "the computed hash is zero."  A common repair is to add a
second cache field, such as `hashIsZero`.  The protocol treats each field
separately:

```text
H = stringHash(a)

Valid_hash(a, h) =
    h = 0
 or (h = H and H != 0)

Valid_hashIsZero(a, z) =
    z = false
 or (z = true and H = 0)
```

The method may use the two fields to avoid repeated recomputation in the
zero-hash case.  The important proof principle is that the fields are not read
from one coherent snapshot.  A read of `hash` and a read of `hashIsZero` are
each individually valid for `a`, but they may come from different points in the
history.  A cache-safe method must be correct for every combination of
individually valid observations.

For example, if a method reads `hashIsZero` into a local variable and returns
`0` when that local variable is true, the return is correct because the protocol
guarantees that `true` is written only when `H = 0`.  If the method reads
`hash` and sees a nonzero value, the value must be `H`.  If the method sees
only unknown sentinels, it recomputes from stable abstract state.  No proof step
requires the two cache fields to agree as a snapshot.

### 2.3 URI-Like Decoded Component Caches

A URI-like object may store raw components as abstract state and lazily cache
decoded components.  The abstract value contains the raw path, raw query, raw
fragment, and raw scheme-specific part.  Cache fields include `decodedPath`,
`decodedQuery`, `decodedFragment`, `decodedSchemeSpecificPart`, and perhaps a
hash cache.  A protocol for an object-valued decoded component has the shape:

```text
Valid_decodedPath(a, v) =
    v = null
 or v = decode(path(a))
```

Each decoded component has its own derived function.  These caches are
independent in the generic theorem: the proof of validity for a `decodedPath`
read uses the history of `decodedPath`, and the proof of validity for a
`decodedQuery` read uses the history of `decodedQuery`.  The method proof may
combine the observed values, but it must not assume that they were all produced
by one synchronized read of the object.

Object-valued caches add one issue that integer caches avoid.  If a cache value
is itself an object, the protocol must account for safe publication and the
stability of the cached object.  This first paper treats that requirement as
part of the cache-validity predicate or as an obligation of a future memory
model instantiation.  The generic theorem says that a read observes a
protocol-valid value.  It does not, by itself, prove that Java safely publishes
the internals of every object-valued cached result.

### 2.4 BigInteger-Like Numeric Caches

Numeric classes often cache expensive derived properties using offset sentinel
encodings.  A BigInteger-like object may have stable mathematical value `n` and
cache fields such as:

```text
bitCountPlusOne     : 0 or bitCount(n) + 1
bitLengthPlusOne    : 0 or bitLength(n) + 1
lowestSetBitPlusTwo : 0 or lowestSetBit(n) + 2
```

Each cache field has a validity predicate of the form `0 or encode(f(a))`.  The
offset avoids ambiguity when the true derived value can be zero or negative
under the source-level API convention.  The proof is the same as for the hash
cache: every history entry must be the sentinel or the encoding of the derived
value for the stable abstract state.  Methods are cache-safe when they either
use a valid cached value after decoding or recompute from the stable abstract
value and write a valid encoding.

These examples should not be proved as unrelated special cases.  They are
instances of one theorem with different cache fields, derived functions,
sentinels, and method-level trace obligations.

## 3. Background

### 3.1 Abstract Immutability and Excluded State

Reference-immutability systems distinguish what can be mutated through a
reference from what the object is allowed to mutate internally.  Systems such
as Javari, IGJ, OIGJ, ReIm, Glacier, Constrictor, and CiFi occupy different
points in this design space [@JAVARI; @IGJ; @OIGJ; @REIM; @GLACIER;
@kinsbruner2024constrictor; @CiFi].  The shared concern is that ordinary
field-level immutability is too blunt for object-oriented programs.  A field
may be mutable because it is a cache, a back pointer, an implementation detail,
or part of a controlled initialization protocol.  A sound immutability theorem
must specify which parts of the reachable object graph constitute the abstract
state.

PICO uses mutability qualifiers and assignability modifiers to define and
protect abstract state.  Its existing Rocq development proves type soundness
and immutability theorems over the PICO core language.  The relevant theorem
for this paper is abstract immutability: fields in the abstract state of an
immutable object are protected, while selected assignable fields may be
excluded from the abstract state.  That theorem justifies the premise
`StableAbs(o, a)`.  It does not need to know how a particular cache protocol
uses excluded fields.

This separation is important.  A stable abstract-state provider answers the
question "what is the value of the object?"  The cache protocol answers "which
mutations of excluded fields are semantically invisible for that value?"  Many
systems besides PICO could supply the first answer: final-field invariants,
ownership invariants, module abstraction, hand-written Iris invariants, or a
deductive verifier.  The derived-cache theorem should not depend on PICO's
syntax or type rules.

### 3.2 Weak Memory and Racy Reads

A sequential interleaving model is not enough for unsynchronized cache fields.
In a simple interleaving semantics, each read sees the current value in a single
global heap.  That model can prove useful facts about benign races under
sequential consistency, but it hides the behavior that makes racy caches
delicate.  Weak memory permits a read to observe a write that is not the most
recent write in a global order, and repeated reads can observe different writes
without intervening synchronization.

The Java Memory Model is the relevant production model for Java-like code
[@manson2005jmm].  It includes synchronization order, happens-before,
final-field rules, and causality constraints.  This paper does not formalize
those rules.  Instead, it extracts a field-history interface: a cache read must
observe some whole value from the write history of the same field, or the
field's initial/default value, and a cache write must extend that history.  We
write this memory-model side condition as `AtomicCacheField(k)`: reads and
writes of cache field `k` are whole-value operations.  The theorem is
parametric in this interface.  A future JMM adequacy theorem would have to
prove that the Java executions under consideration satisfy it, including
default writes, initialization, final-field freeze actions, atomicity, and
causality.

The interface is weak enough to model stale observations and independent reads.
It is strong enough to rule out reads of values that were never written.  It
also avoids torn values.  For Java, that excludes plain non-volatile `long` and
`double` cache fields by default, because such accesses may be treated as two
32-bit halves.  It is satisfied by `int`, `boolean`, and reference cache fields,
and by `long` or `double` fields only when accessed through `volatile`,
synchronization, an atomic wrapper, or another mechanism that guarantees
whole-value reads and writes.

### 3.3 Iris and Rocq

Iris is a higher-order concurrent separation logic framework mechanized in Coq,
now Rocq [@jung2015iris; @jung2018iris].  It provides invariants, ghost state,
and weakest-precondition reasoning for concurrent programs.  Prior work has
used separation-logic techniques to reason about weak memory, including GPS and
Iris-based release-acquire reasoning [@turon2014gps; citation needed for
specific Iris RA/iRC11/Cosmo-style systems].

The development in this paper uses Iris in a staged way.  The generic cache
theory is first mechanized as ordinary Rocq propositions.  Iris-facing files
wrap those propositions as pure Iris assertions and introduce invariant and
state-interpretation boundaries for later WP proofs.  This is a deliberate
architecture: the generic semantic theorem should be understandable without
Iris, while Iris supplies the proof infrastructure for integrating the theorem
with concurrent program reasoning.

## 4. Core Language and Execution Abstraction

The theorem does not require full Java.  It requires a minimal object or record
model with stable abstract fields, excluded cache fields, methods that read and
write cache fields, and executions that produce cache-read traces.

Let `Obj` be the type of object identities or records, and let `AbsVal` be the
type of abstract values.  A stable abstraction provider is a predicate:

```text
StableAbs : Obj -> AbsVal -> Prop
```

`StableAbs(o, a)` means that `o` has fixed abstract value `a`.  The predicate is
not defined by the generic theorem.  It is supplied by PICO, by an Iris
invariant, or by another proof system.

A program state contains field histories for excluded cache fields.  For each
object `o` and cache field `k`, `Hist(o, k)` is a list of values written to
that field.  The initial history includes the default write.  A cache write
appends a value to the corresponding history.  A cache read produces an
observation:

```text
obs = read(o, k, v)
```

and the memory interface supplies:

```text
read(o, k, v) -> v in Hist(o, k)
```

The interface intentionally does not say that `v` is the last value in the
history.  It also does not impose coherence between two observations in the
same trace.  A method execution records the sequence of cache observations that
affect the method.  That sequence is a cache-read trace.

The core calculus can be presented as a small command language:

```text
e ::= x | c | readAbs(o, f) | readCache(o, k)
s ::= skip
    | x := e
    | writeCache(o, k, e)
    | s; s
    | if x then s else s
    | return e
```

The calculus distinguishes abstract-state reads from cache reads.  Abstract
state is stable by premise; excluded cache state is governed by protocols.
The generic theorem does not require a source-level type system, inheritance,
method dispatch, exceptions, or Java expressions.  PICO supplies those features
in its own formalization and then exports the stable abstraction fact needed by
the cache theorem.

The execution abstraction has four roles.

First, it records cache reads as traces.  A method may be interpreted as a
function from an abstract value, ordinary arguments, and a cache-read trace to a
result plus a list of cache writes.  This trace semantics is not a full
operational semantics; it is a specification interface for method robustness.

Second, it records writes as cache observations for proof purposes.  A write is
safe when the value written is valid under the protocol for the stable abstract
value.

Third, it separates abstract-state preservation from cache-history
preservation.  `StableAbs(o, a)` is preserved because cache-safe methods do not
write abstract-state fields.  `CacheHistOK(P, o, a)` is preserved because every
cache write is valid for `a`.

Fourth, it isolates memory-model obligations.  The cache theorem assumes
read-from-history and write-extends-history.  It does not commit to how a
particular memory model proves those facts.

## 5. Generic Cache Protocol

A cache protocol packages the fields and validity predicates for a family of
excluded caches:

```text
CacheProtocol P contains:
  cache_field(P)        the cache fields governed by P
  cache_val(P, k)       the value type of field k
  default(P, k)         the default or unknown value of k
  Valid_k(a, v)         whether value v is valid for abstract value a

Requirement:
  Valid_k(a, default(P, k)) for every a and k.
```

The default-validity requirement reflects the fact that newly allocated objects
begin with default cache values.  It does not require the default to be a
completed derived value.  It only requires the method proof to treat the
default as unknown.

Given a protocol `P`, a history function `Hist`, an object `o`, and an abstract
value `a`, the cache-history invariant is:

```text
CacheHistOK(P, Hist, o, a) =
  forall k v.
    v in Hist(o, k) -> Valid_k(a, v)
```

The trace validity predicate lifts field validity to observations:

```text
ValidObs(P, a, obs(k, v)) = Valid_k(a, v)

ValidTrace(P, a, trace) =
  every observation in trace is a ValidObs(P, a)
```

The semantic immutability predicate combines stable abstract state and valid
cache histories:

```text
SemImm(P, Hist, StableAbs, o, a) =
  StableAbs(o, a) * CacheHistOK(P, Hist, o, a)
```

In paper notation, when `Hist` and `StableAbs` are clear, we write
`SemImm(P, o, a)`.

The first key lemma is read validity:

```text
Lemma Cache Read Validity.
If CacheHistOK(P, Hist, o, a)
and read_cache(o, k, v)
and read_cache(o, k, v) implies v in Hist(o, k),
then Valid_k(a, v).
```

The second key lemma lifts this pointwise result to traces:

```text
Lemma Valid Trace from History.
If CacheHistOK(P, Hist, o, a)
and every observation in trace reads from the corresponding field history,
then ValidTrace(P, a, trace).
```

These lemmas explain why histories are necessary.  If the invariant mentioned
only the current heap value, a stale read could observe an older invalid value
that is no longer current.  By requiring every history entry to be valid, the
invariant covers stale reads, repeated reads, and reordering effects abstractly.

The history invariant is also modular across fields.  A protocol may govern one
field or many fields.  `CacheHistOK` quantifies over all governed fields, but a
read of field `k` uses only `Hist(o, k)`.  Multi-field protocols therefore
support independent cache fields without requiring a global snapshot relation.

## 6. Cache-Safe Methods

The method-level proof obligation is `CacheSafe(m, P, F)`.  Here `F` is the
pure specification:

```text
F : AbsVal -> Args -> Result
```

For a String-like `hashCode`, `F(a, ()) = stringHash(a)`.  For a URI-like
decoded path accessor, `F(a, ()) = decode(path(a))`.  For a BigInteger-like
bit-count method, `F(a, ()) = bitCount(a)`.

The generic mechanization represents a method by its behavior under an
arbitrary cache-read trace:

```text
run_with_cache_trace(a, args, trace) =
  { result = r; writes = write_trace }
```

The cache-safe method judgment requires:

```text
CacheSafe(m, P, F) iff
  for every a, args, and trace,
  if ValidTrace(P, a, trace), then
    result(m, a, args, trace) = F(a, args)
    and every cache write performed by m is valid for a.
```

In a fuller source-language presentation, `CacheSafe` has the following
components.

1. The method does not write abstract-state fields.

2. The method writes only excluded cache fields governed by `P`, or fields
   proven irrelevant by a separate framing argument.

3. Every cache write is valid for the stable abstract value.  For derived
   caches, this usually means the value is computed from stable abstract state,
   not from arbitrary racy observations.

4. The method returns `F(a, args)` for every valid cache-read trace.

5. The method does not rely on two reads of the same racy field observing the
   same write.

6. The method does not assume that reads of multiple cache fields form a
   coherent global snapshot.

The fourth condition is the most distinctive.  It turns weak-memory complexity
into a trace quantification.  Instead of proving the method correct for one
interleaving or one heap sequence, the proof considers every sequence of
observations allowed by the protocol.

The bad hash implementation fails this judgment.  The trace
`[hash = H, hash = 0]` is valid when `H != 0`, but the implementation returns
`0`.  Therefore `CacheSafe` is false.  The local-copy implementation satisfies
the judgment because its result depends on at most one racy read of `hash`.
When that read is unknown, the method recomputes from stable abstract state.
When that read is known, the protocol guarantees that it is the correct hash.

Trace robustness also clarifies how to reason about cache writes.  A cache
write must be causally grounded in stable abstract state.  It is not enough to
write a value obtained from an arbitrary racy read unless the protocol proves
that the value is valid for `a`.  This rule avoids circular justifications in
which a method reads an invalid value and then writes it back, thereby making
the history appear valid after the fact.  The history invariant is preserved
only when every appended value is valid before the append.

## 7. Main Theorems

This section states the main results in theorem/proof-sketch form.  The
statements are phrased at the generic level and then specialized later to PICO.

### 7.1 Cache Read Validity

```text
Theorem Cache Read Validity.
For any protocol P, history Hist, object o, abstract value a,
cache field k, and value v,
if
  CacheHistOK(P, Hist, o, a)
  and ReadFromHistory(read_cache, Hist)
  and read_cache(o, k, v),
then
  Valid_k(a, v).
```

Proof sketch.  The memory interface gives `v in Hist(o, k)`.  The
`CacheHistOK` invariant says that every value in `Hist(o, k)` is valid for `a`.
Applying the invariant to `v` yields `Valid_k(a, v)`.

### 7.2 Valid Trace from History

```text
Theorem Valid Trace from History.
For any trace trace,
if
  CacheHistOK(P, Hist, o, a)
  and every observation in trace reads from the corresponding field history,
then
  ValidTrace(P, a, trace).
```

Proof sketch.  Induct over the trace.  For each observation, apply cache read
validity.  The empty trace is valid by definition.

### 7.3 Cache History Preservation

```text
Theorem Cache History Preservation.
Suppose CacheHistOK(P, Hist, o, a) holds.
If a transition writes only values v to governed cache fields k
such that Valid_k(a, v), and leaves abstract state unchanged,
then the extended history Hist' also satisfies CacheHistOK(P, Hist', o, a).
```

Proof sketch.  For each field history, either the transition does not write the
field, in which case the history is unchanged, or it appends a valid value.  Old
entries remain valid by the induction hypothesis; the new entry is valid by the
transition premise.  Abstract-state preservation is separate and follows from
the no-abstract-write condition or from the stable abstraction provider.

### 7.4 Derived-Cache Method Soundness

```text
Theorem Derived-Cache Method Soundness.
For any object o, abstract value a, cache protocol P, method m,
and pure specification F,
if
  StableAbs(o, a),
  CacheHistOK(P, Hist, o, a),
  MemoryModelInterface(Hist),
  CacheSafe(m, P, F),
and an execution of m(o, args) observes a trace trace allowed by
the memory interface,
then the execution returns F(a, args) and preserves SemImm(P, o, a).
```

In the compact form used by the Rocq core:

```text
StableAbs(o, a)
and CacheHistOK(P, Hist, o, a)
and CacheSafe(m, P, F)
and ValidTrace(P, a, trace)
and weak_exec_matches_trace(m, a, args, trace, r)
imply
  r = F(a, args)
  and SemImm(P, Hist, StableAbs, o, a).
```

Proof sketch.  The memory interface and cache-history invariant imply
`ValidTrace(P, a, trace)`.  The `CacheSafe` premise applied to this trace gives
the result equality and validity of writes.  Cache-history preservation uses
write validity.  Stable abstract state is preserved because the method does not
write abstract-state fields and the stable abstraction provider remains true.
Combining these facts yields `SemImm`.

### 7.5 Refinement to Pure Recomputing Implementation

```text
Theorem Cached-to-Pure Refinement.
Let m_cached be a cache-safe implementation for protocol P and pure
specification F.  Let m_pure(o, args) return F(a, args) whenever
StableAbs(o, a).  Under SemImm(P, o, a), every observable result of
m_cached(o, args) is an observable result of m_pure(o, args), and the
post-state again satisfies SemImm(P, o, a).
```

Proof sketch.  Method soundness gives that every execution of `m_cached`
returns `F(a, args)`.  The pure method returns the same value by definition.
Cache writes are hidden from clients and preserve `SemImm`, so clients cannot
distinguish the cached implementation from recomputation by observing public
results or abstract state.

The refinement is intentionally termination-insensitive in the first
formulation: it compares returned values for terminating executions.  A
termination-sensitive version would need additional obligations showing that
cache code does not introduce divergence, blocking, or exceptions.  For the
simple derived-cache methods considered here, those obligations are usually
straightforward but are not the central contribution.

### 7.6 Class-Level Abstraction Theorem

```text
Theorem Class-Level Semantic Immutability.
Consider a class or abstraction whose public methods are all cache-safe
with respect to protocol P, whose excluded cache fields are hidden from
clients, and whose constructors establish StableAbs and CacheHistOK.
Then the cached implementation contextually refines the pure implementation
that recomputes all derived values from the stable abstract state.
```

Proof sketch.  Constructors establish `SemImm`.  Each public method preserves
`SemImm` and returns the pure result by method soundness.  Hidden cache fields
prevent clients from observing cache histories directly.  The proof proceeds by
standard simulation over client-visible method calls.  Every cached step
corresponds to a pure recomputing step with the same public result and the same
abstract state.

## 8. PICO Instantiation

PICO is an instantiation of the stable abstract-state provider, not the whole
derived-cache theory.  Its role is to identify the abstract-state fields of an
object and prove that those fields are protected.  The generic cache theorem
then reasons about excluded mutable fields.

At a high level, the PICO theorem supplies:

```text
PICOStableAbs(o, a)
```

where `a` is the tuple or structured value obtained by reading the abstract-
state fields of `o`.  The PICO proof establishes that, for an object protected
by the relevant immutability qualifier and method scope, evaluation preserves
the abstract-state field values.  Assignable cache fields are outside the
abstract reachability relation used to define `a`.

The bridge from PICO to the generic theorem has three steps.

First, ordinary Rocq PICO theorems prove field-level stability.  In the current
artifact, `DeepImmutability.v`, `ReadonlySafety.v`, and related files provide
the core immutability theorems, while `DerivedCache.v` proves a sequential
derived-cache update shape for final abstract fields and assignable integer
cache fields.

Second, the PICO stable abstraction is packaged as a pure predicate.  In the
generic derived-cache instance, the provider hook has the shape:

```text
pico_stable_abs(CT, C, abs_fields, (h, loc), abs_vals) =
  final_fields(CT, C, abs_fields)
  and field_reads(h, loc, abs_fields, abs_vals)
```

This is a small provider used by the current generic cache bridge.  It is not a
replacement for the full PICO immutability theorem.  Rather, it is the point at
which a PICO theorem about abstract-field stability can be exposed to the
generic cache layer.

Third, Iris-facing wrappers import the pure fact.  The wrapper does not rewrite
PICO in Iris.  It turns the existing Rocq theorem into an Iris pure assertion,
for example:

```text
StableAbsI Stable o a = pure(Stable o a)
CacheHistOKI P Hist o a = pure(CacheHistOK P Hist o a)
SemImmI P Hist Stable o a = StableAbsI Stable o a * CacheHistOKI P Hist o a
```

This division keeps the proof architecture modular.  PICO remains responsible
for abstract-state immutability.  The Iris/Rocq cache wrapper remains
responsible for histories, protocols, read validity, trace robustness, and
refinement to pure recomputation.

The division also prevents an overclaim.  PICO's existing abstract immutability
theorem does not prove that every Java racy cache execution is safe.  It proves
that abstract-state fields are protected under the PICO model.  The derived-
cache theorem adds a separate condition: excluded cache writes must obey a
protocol, and methods must be correct for every valid cache-read trace.

## 9. Iris/Rocq Mechanization

The artifact is organized as a staged development rather than a single monolithic
proof.  The important boundary is between what is mechanized now and what is
future work.

### 9.1 Existing PICO Core

The PICO core remains unchanged.  The top-level theorem map in the repository
identifies the existing proof entry points:

```text
Preservation.v              preservation_pico
DeepImmutability.v          shallow_immutability_pico
                             deep_immutability_pico
ReadonlySafety.v            readonly_pico_field_write
                             readonly_method_call_preserves_arguments
ConcreteImmutability.v      ConcreteImmutability
WFNOMutationEXP.v           well_typed_no_mutation_exp
```

These theorems establish type soundness and immutability properties for the
PICO core language.  They do not contain the generic field-history theorem.

### 9.2 Generic Cache Protocol Core

`GenericCacheProtocol.v` is PICO-independent.  It defines:

```text
StableAbs
CacheProtocol
CacheHistory
CacheHistOK
CacheObs
CacheTrace
ValidObs
ValidTrace
TraceReadsFromHistory
CacheRun
CacheSafeMethod
SemImm
```

It proves:

```text
cache_read_valid
valid_trace_from_history
cache_safe_method_sound
cache_safe_method_sound_from_history
```

These are the mechanized core of the generic theorem.  They are intentionally
small.  The goal is not to encode all Java behavior in this file, but to state
and prove the reusable semantic fact precisely.

### 9.3 Derived-Cache Instance and Hash Traces

`GenericDerivedCache.v` instantiates the generic protocol with current PICO
values and derived integer caches.  It includes:

```text
derived_cache_protocol
wm_derived_cache_history
wm_derived_cache_read
wm_derived_cache_read_from_history
wm_read_valid_via_generic_cache_hist_ok
```

It also mechanizes the motivating hash-cache distinction:

```text
bad_hash_trace_valid
bad_hash_trace_returns_wrong
bad_hash_not_cache_safe
good_hash_cache_safe_method
```

These lemmas match the paper's negative example.  The bad double-read method is
rejected because a valid trace can make it return the wrong result.  The
local-copy method is accepted because it is correct for every valid trace in
the modeled protocol.

### 9.4 Field-History Memory Interface

`PicoMemoryModel.v` begins the weak-memory layer.  It defines field addresses,
write messages, field histories, weak-memory state, and a parameterized
`CacheMemoryModel` class:

```text
wm_read : wm_state -> view -> FieldAddr -> value -> view -> Prop

wm_read_from_history :
  wm_read sigma V addr v V' ->
  exists msg, msg in history_of(sigma, addr) and msg_val(msg) = v
```

It also defines weak writes that append to histories and proves preservation
and read-validity endpoints for allowed cache writes, including:

```text
wm_steps_preserve_cache_history_from_allowed_writes
wm_steps_read_valid_from_allowed_writes
wm_steps_preserve_cache_history_from_config_allowed
wm_steps_read_valid_from_config_allowed
```

This layer is a field-history execution abstraction.  It is not a Java Memory
Model formalization.

### 9.5 Iris Wrappers and State Boundaries

`GenericCacheIris.v` wraps the generic theorem in Iris propositions:

```text
StableAbsI
CacheHistOKI
ValidTraceI
CacheSafeMethodI
SemImmI
CacheMethodPostI
cache_read_validI
valid_trace_from_historyI
cache_safe_method_soundI
cache_safe_method_sound_from_historyI
```

`GenericDerivedCacheIris.v` exposes the derived-cache read-validity bridge as a
pure Iris fact.  The later PICO Iris files go beyond pure wrappers by adding a
minimal Iris language instance for weak-memory PICO threads, an invariant over
cache-history validity, ghost-state facades, WP state-bridge contracts, and
logical-relation-facing wrappers.  These files give stable theorem boundaries
for a future full WP/logical-relation development.

The current paper should claim the generic Rocq theorem and the Iris-facing
wrapper/invariant architecture.  It should not claim a complete ghost-backed
Iris logical relation for all PICO types, nor a full Java weak-memory
adequacy theorem.

### 9.6 Mechanized and Not Mechanized

Mechanized in the current core:

1. Generic definitions of stable abstraction providers, cache protocols,
   cache-history validity, valid traces, cache-safe methods, and semantic
   immutability.

2. Read-from-history soundness: a cache read from a valid history observes a
   protocol-valid value.

3. Trace validity from history reads.

4. Method soundness for trace-robust cache-safe methods.

5. A derived integer-cache instance and PICO stable-abstraction hook.

6. The bad hash-cache trace counterexample and the local-copy accepted proof
   shape.

7. Field-history memory-interface lemmas for append-only writes and read
   validity after allowed-write executions.

8. Iris-facing pure wrappers and staged invariant/state-interpretation
   boundaries.

Not mechanized in the current core:

1. Full Java Memory Model executions.

2. Happens-before, synchronization order, causality validation, or
   out-of-thin-air prevention.

3. Final-field freeze actions and Java initialization safety.

4. A production Java checker for arbitrary cache-safe methods.

5. Full OpenJDK verification.

6. A complete ghost-backed Iris logical relation proving all PICO typing rules
   against the weak-memory state interpretation.

These non-claims are part of the theorem statement, not caveats added after the
fact.  The proof is designed to be memory-model-parametric.

## 10. Weak-Memory Discussion

The field-history interface deliberately abstracts from the hardest parts of
the Java Memory Model.  This section explains what is abstracted and why the
abstraction is still useful.

### 10.1 Happens-Before

Happens-before relates synchronization actions, program order, and visibility
guarantees in Java.  Synchronization can restrict which writes a read may
observe.  Derived caches of the kind considered here often omit
synchronization, so the proof cannot rely on happens-before ordering between
cache writes and cache reads.

The generic theorem requires only a weaker property: if a cache read observes
`v`, then `v` appears in the field's write history.  A concrete memory model may
use happens-before and synchronization to prove a stronger read restriction,
but the cache theorem does not require that strength.

### 10.2 Causality and Out-of-Thin-Air Values

Weak-memory models must prevent unjustified reads, especially out-of-thin-air
values produced by circular reasoning.  The generic theorem does not implement
such a causality check.  It assumes a memory interface that supplies grounded
read-from-history observations.  If a value was never written to the cache
field, it cannot be read through this interface.

Cache writes have an additional proof obligation: they must be valid for stable
abstract state before they are appended to the history.  A method cannot
justify a cache write merely by reading a racy value and copying it unless the
value is already known to satisfy the protocol.  This condition reduces the
risk of circular justification at the cache-protocol level.  It is not a
replacement for a memory-model causality theorem.

### 10.3 Final Fields and Stable Abstract State

String-like examples usually rely on stable payload fields.  In Java, final
fields have special initialization and visibility rules.  This paper treats
that stability as part of the `StableAbs` premise.  PICO can supply stable
abstract state in its model by proving abstract-state immutability.  A future
JMM instantiation would need to connect Java final-field initialization and
freeze actions to the same premise.

The distinction matters.  The cache theorem says: if the abstract value is
stable, and cache writes are valid for that abstract value, then cache mutation
is semantically invisible.  It does not prove that Java final fields are
properly initialized in every program.

### 10.4 Atomicity and Tearing

The field-history interface assumes whole-value reads:

```text
Whole-value reads.
  If read(o.k) returns v, then v is the value of some complete write to o.k,
  or the initial/default value of o.k.
```

Equivalently, each admissible cache field must satisfy `AtomicCacheField(k)`.
The interface does not model torn reads.  A Java instantiation must therefore
check admissibility for each cache field.  Plain `int`, `boolean`, and
reference cache fields are admissible at the level of the cached value itself:
the read returns one whole primitive value or one whole reference.  Plain
non-volatile `long` and `double` cache fields are not admissible by default,
because a racy read may combine halves of two different writes and produce a
value that is not in the history of whole writes.  Such fields require a
stronger mechanism such as `volatile`, `synchronized`, `AtomicLong`,
`AtomicReference`, or a verified multi-field protocol that explicitly models
the representation.

This side condition is separate from Java's no-word-tearing rule.  No word
tearing supports the artifact's field-address model by ensuring that updates to
one field or array element do not corrupt another field or element.  The
whole-value condition additionally says that a read of one admissible cache
field observes one complete value from that field's own history.

### 10.5 Required Future JMM Adequacy Theorem

A future Java Memory Model instantiation should prove an adequacy theorem of
the following shape:

```text
Theorem JMM-to-Field-History Adequacy.
For the class of cache fields and executions under consideration,
every JMM-legal execution induces field histories such that:
  1. default writes initialize histories;
  2. each cache write appends a whole value to the relevant history;
  3. each cache read observes a whole value from that history;
  4. stable abstract state is justified by initialization/final-field/
     immutability premises;
  5. causality rules exclude reads not grounded in the execution.
```

Only after such a theorem is proved should the result be described as Java
Memory Model soundness.  The present paper proves the memory-parametric theorem
that such an adequacy result would instantiate.

## 11. Case Studies

The case studies are proof sketches and protocol instantiations, not full
OpenJDK verifications.  Their purpose is to show that the theorem captures a
family of derived caches with one abstraction.

### 11.1 String-Like `hashCode`

Abstract state:

```text
a = string contents
```

Excluded cache fields:

```text
hash       : int
hashIsZero : boolean
```

Derived function:

```text
H = stringHash(a)
```

Protocol:

```text
Valid_hash(a, h) =
    h = 0
 or (h = H and H != 0)

Valid_hashIsZero(a, z) =
    z = false
 or (z = true and H = 0)
```

Cache-safe method shape:

```java
int h = hash;
if (h != 0) {
    return h;
}
if (hashIsZero) {
    return 0;
}
h = computeHashFromStableAbstractState();
if (h == 0) {
    hashIsZero = true;
} else {
    hash = h;
}
return h;
```

This sketch is not meant as a prescriptive implementation.  It illustrates the
proof obligations.  If the method reads `hash` as nonzero, the protocol gives
`h = H`.  If it reads `hashIsZero` as true, the protocol gives `H = 0`.  If it
sees only unknown values, it computes from stable contents.  The writes
`hashIsZero = true` and `hash = h` are valid because they occur only after
computing `H` from the stable abstract state.

The proof does not assume that the read of `hash` and the read of `hashIsZero`
come from one snapshot.  Each observation is justified independently by its
field history.

### 11.2 URI-Like Decoded Components

Abstract state:

```text
a = raw URI components
    { rawPath, rawQuery, rawFragment, rawSchemeSpecificPart, ... }
```

Excluded cache fields:

```text
decodedPath
decodedQuery
decodedFragment
decodedSchemeSpecificPart
hash
```

Derived functions:

```text
decodePath(a) = decode(rawPath(a))
decodeQuery(a) = decode(rawQuery(a))
decodeFragment(a) = decode(rawFragment(a))
decodeSSP(a) = decode(rawSchemeSpecificPart(a))
uriHash(a) = hash of normalized abstract URI value
```

Protocols:

```text
Valid_decodedPath(a, v) =
    v = null or v = decodePath(a)

Valid_decodedQuery(a, v) =
    v = null or v = decodeQuery(a)

Valid_decodedFragment(a, v) =
    v = null or v = decodeFragment(a)

Valid_decodedSchemeSpecificPart(a, v) =
    v = null or v = decodeSSP(a)

Valid_hash(a, h) =
    h = 0 or (h = uriHash(a) and uriHash(a) != 0)
```

The decoded-component accessors are cache-safe if they either return a non-null
cached value known valid by the protocol or compute the decoded value from raw
abstract components and write it.  The proof for each accessor is an instance
of method soundness.  Methods that combine multiple decoded components must be
trace robust across fields.  For example, a method may read a cached path and a
cached query from different points in the history; it can use them together
only because each is separately a deterministic function of the same stable raw
URI abstract value.

Object-valued caches require a validity predicate strong enough to include the
semantic value of the cached object and its publication safety.  In a first
formalization, this can be represented abstractly:

```text
Valid_decodedPath(a, v) =
    v = null
 or PublishedString(v, decodePath(a))
```

where `PublishedString` is supplied by a separate invariant or memory-model
instantiation.

### 11.3 BigInteger-Like Numeric Caches

Abstract state:

```text
a = mathematical integer represented by the object
```

Excluded cache fields:

```text
bitCountPlusOne
bitLengthPlusOne
lowestSetBitPlusTwo
```

Derived functions and encodings:

```text
BC = bitCount(a)
BL = bitLength(a)
LSB = lowestSetBit(a)

encodeBC(BC) = BC + 1
encodeBL(BL) = BL + 1
encodeLSB(LSB) = LSB + 2
```

Protocols:

```text
Valid_bitCountPlusOne(a, v) =
    v = 0 or v = bitCount(a) + 1

Valid_bitLengthPlusOne(a, v) =
    v = 0 or v = bitLength(a) + 1

Valid_lowestSetBitPlusTwo(a, v) =
    v = 0 or v = lowestSetBit(a) + 2
```

Accessor methods decode cached values when nonzero and recompute otherwise.
For example, a bit-count method reads `bitCountPlusOne` into a local variable
`b`.  If `b != 0`, it returns `b - 1`; by the protocol this is `bitCount(a)`.
If `b == 0`, it computes `bitCount(a)`, writes `bitCount(a) + 1`, and returns
`bitCount(a)`.  The write is valid by construction.

The three numeric caches are independent fields under one protocol.  A method
that reads more than one must handle every combination of sentinel and encoded
valid values.  It may not assume that one cached value being initialized means
another cache field has also been initialized.

### 11.4 Case-Study Summary

The examples differ in value type, sentinel choice, and method logic, but they
share one proof pattern:

```text
StableAbs(o, a)
CacheHistOK(P, o, a)
read-from-history memory interface
CacheSafe(m, P, F)
----------------------------------
m refines pure recomputation F(a, args)
```

The theorem therefore avoids a collection of ad hoc "benign race" arguments.
Each cache is safe only when its protocol and method proof satisfy the generic
conditions.

## 12. Related Work

### 12.1 Abstract and Reference Immutability

Javari introduced reference immutability for Java and includes support for
assignable fields, which are a direct predecessor of the excluded-cache fields
studied here [@JAVARI].  IGJ and OIGJ use Java generics to encode object and
ownership immutability [@IGJ; @OIGJ].  ReIm focuses on reference immutability
and inference of method purity [@REIM].  Glacier explores transitive class
immutability for Java [@GLACIER].  CiFi analyzes class and field immutability
with fine-grained assignability information [@CiFi].  Constrictor distinguishes
view object immutability from transitive state using model checking
[@kinsbruner2024constrictor].

PICO belongs to this family but provides the stable abstraction provider used
by this paper.  It identifies abstract-state fields, proves abstract-state
immutability, and treats excluded cache fields as outside abstract
reachability.  The new theorem is not another reference-immutability type
system.  It is a semantic wrapper that explains when excluded cache mutation is
unobservable under racy reads.

### 12.2 Benign Data Races and Lazy Initialization

The term "benign data race" is often used for racy code whose behavior is
intended to be harmless [@benign_races].  Lazy initialization and memoization
are common examples.  This paper narrows the claim.  A racy cache is not benign
merely because the field is private or because all writes compute "the same"
value in a sequential argument.  The method must be correct for every valid
cache-read trace.  The bad hash example demonstrates that individually valid
observations can still compose into an invalid result when a method double
reads a racy field.

### 12.3 Java Memory Model and Relaxed Memory

The Java Memory Model defines the allowed behaviors of Java programs under
concurrency, including happens-before and causality [@manson2005jmm].  Work on
promising semantics addresses relaxed-memory causality and out-of-thin-air
concerns in a different formal setting [@kang2017promising].  C/C++11 memory
model repair work illustrates how subtle the interaction between language
memory models and intuitive sequential reasoning can be [@lahav2017repairing].

This paper does not compete with those models.  It abstracts over them.  The
field-history interface is a small adequacy target for a future Java Memory
Model proof.  The result says that if a memory model supplies read-from-history
executions and if cache writes are valid for stable abstract state, then the
cache is semantically invisible.  It does not say that the current mechanized
model accepts exactly the Java executions.

### 12.4 Weak-Memory Separation Logics

GPS uses ghosts, protocols, and separation logic to reason about weak-memory
programs [@turon2014gps].  Iris provides a general framework for higher-order
concurrent separation logic and has supported many later verification
developments [@jung2015iris; @jung2018iris].  Iris-based logics for release-
acquire or RC11-style reasoning are closely related in proof technology
[citation needed for exact iRC11/Cosmo references].

The present work uses Iris differently.  Rather than building a full weak-
memory program logic first, it isolates a cache-specific semantic theorem and
wraps it in Iris predicates.  The theorem can later be connected to a richer
Iris memory model, but the core proof does not depend on that model.

### 12.5 Semantic Type Soundness and Logical Relations

Semantic type soundness proofs and logical relations often show that typed
programs refine a specification or preserve an invariant in a semantic model
[@milner1978theory; citation needed for modern semantic type soundness surveys].
RustBelt is a prominent example of using Iris to prove semantic soundness for a
realistic language core with libraries that use unsafe features [@jung2018rustbelt].

The derived-cache theorem has a similar shape: a syntactic or external proof
system supplies stable abstract state and method safety, while the semantic
model proves refinement to pure behavior.  The novelty is the history-based
protocol for excluded racy caches and the trace-robust method obligation.

## 13. Limitations and Future Work

The first limitation is memory-model scope.  The mechanized core is not a full
Java Memory Model formalization.  Happens-before, synchronization order,
causality validation, out-of-thin-air prevention, final-field freeze actions,
default initialization in the full Java object model, and complete execution
validation are outside the current proof.  The theorem is parameterized by a
field-history interface.  A future JMM instantiation must prove that the class
of Java executions under consideration satisfies that interface.

The second limitation is checker support.  The paper does not provide a
production Java checker that verifies `CacheSafe` for arbitrary methods.  The
current mechanization proves generic theorem shapes and representative method
patterns.  Automating trace-robust proofs is future work.  A practical checker
would need to identify local-copy patterns, prove that cache writes are derived
from stable abstract state, and reject methods that depend on repeated racy
reads agreeing.

The third limitation is object-valued caches.  Integer caches can be modeled as
whole values with simple validity predicates.  Caches that store object
references require additional publication and representation predicates.  A
URI-like decoded string cache, for example, should not merely prove that the
reference identity was written; it should prove that the referenced string
represents the decoded component and is safely published.  This paper treats
that obligation as part of `Valid_k(a, v)` or as a premise for a future memory
model instantiation.  Atomicity of a reference only rules out torn references;
it does not by itself prove that the pointed-to object was safely initialized.
For object-valued caches, the cached object must itself satisfy an appropriate
stable-abstraction, final-field, immutable-object, or safe-publication
condition.

The fourth limitation is case-study depth.  The String-like, URI-like, and
BigInteger-like examples are protocol instantiations and proof sketches.  They
are not full OpenJDK verifications.  A full library verification would require
source-level modeling of each class, constructor, method, object-valued cache,
and Java memory behavior.

The fifth limitation is the staged Iris development.  The artifact contains
pure Iris wrappers, invariant boundaries, ghost-state facades, WP-state bridge
contracts, and logical-relation-facing endpoints.  It does not yet complete a
full ghost-backed Iris logical relation for all PICO typing rules over the
weak-memory state.

Future work follows directly from these limits.  The first direction is a Java
Memory Model adequacy theorem for the field-history interface.  The second is a
source-level cache-safety checker or proof automation tactic.  The third is a
library-scale verification of more cache patterns, including object-valued
caches and multi-field protocols.  The fourth is deeper integration with Iris
weak-memory logics, replacing pure wrappers with ghost-backed WP rules where
the additional proof power is needed.

## 14. Conclusion

Racy derived caches are safe only under a semantic condition.  The cache fields
must be excluded from abstract state, every value ever written to them must be
valid for the stable abstract value, and every method that reads them must be
correct for every valid cache-read trace.  The current heap value is not the
right invariant under weak memory.  The right invariant is history validity.

This paper gives a generic theorem for that condition.  `StableAbs(o, a)` fixes
the abstract value.  `CacheHistOK(P, o, a)` ensures that cache histories contain
only protocol-valid values.  A read-from-history memory interface turns valid
histories into valid observations.  `CacheSafe(m, P, F)` ensures that methods
are robust to all valid observation traces and write only valid cache values.
Together these premises imply `SemImm(P, o, a)` preservation and refinement to
pure recomputation.

PICO supplies one stable abstract-state provider.  The Iris/Rocq cache wrapper
proves the generic semantic fact around it.  The result is deliberately not a
full Java Memory Model theorem.  It is a smaller theorem that makes the required
memory assumption explicit and reusable: stable abstract state plus valid cache
histories implies semantic immutability for trace-robust derived caches.

## References (working)

The reference list is intentionally conservative.  Entries marked
`[citation needed]` are placeholders that should be resolved before submission.

[@JAVARI] Matthew S. Tschantz and Michael D. Ernst. 2005. Javari: Adding
reference immutability to Java. OOPSLA. DOI: 10.1145/1094811.1094828.

[@IGJ] Yoav Zibin, Alex Potanin, Mahmood Ali, Shay Artzi, Adam Kiezun, and
Michael D. Ernst. 2007. Object and reference immutability using Java generics.
FSE.

[@OIGJ] Yoav Zibin, Alex Potanin, Paley Li, Mahmood Ali, and Michael D. Ernst.
2010. Ownership and immutability in generic Java. OOPSLA.

[@REIM] Wei Huang, Ana Milanova, Werner Dietl, and Michael D. Ernst. 2012.
ReIm and ReImInfer: Checking and inference of reference immutability and method
purity. OOPSLA. DOI: 10.1145/2384616.2384680.

[@GLACIER] Michael Coblenz, Whitney Nelson, Jonathan Aldrich, Brad Myers, and
Joshua Sunshine. 2017. Glacier: Transitive class immutability for Java. ICSE.
DOI: 10.1109/ICSE.2017.52.

[@CiFi] Tobias Roth, Dominik Helm, Michael Reif, and Mira Mezini. 2021. CiFi:
Versatile analysis of class and field immutability. ASE. DOI:
10.1109/ASE51524.2021.9678903.

[@kinsbruner2024constrictor] Elad Kinsbruner, Shachar Itzhaky, and Hila
Peleg. 2024. Constrictor: Immutability as a design concept. ECOOP.

[@benign_races] Satish Narayanasamy, Zhenghao Wang, Jordan Tigani, Andrew
Edwards, and Brad Calder. 2007. Automatically classifying benign and harmful
data races using replay analysis. PLDI.

[@manson2005jmm] Jeremy Manson, William Pugh, and Sarita V. Adve. 2005. The
Java memory model. POPL. DOI: 10.1145/1040305.1040336.

[@kang2017promising] Jeehoon Kang, Chung-Kil Hur, Ori Lahav, Viktor Vafeiadis,
and Derek Dreyer. 2017. A promising semantics for relaxed-memory concurrency.
POPL. DOI: 10.1145/3009837.3009850.

[@lahav2017repairing] Ori Lahav, Viktor Vafeiadis, Jeehoon Kang, Chung-Kil Hur,
and Derek Dreyer. 2017. Repairing sequential consistency in C/C++11. PLDI.
DOI: 10.1145/3062341.3062352.

[@jung2015iris] Ralf Jung, David Swasey, Filip Sieczkowski, Kasper Svendsen,
Aaron Turon, Lars Birkedal, and Derek Dreyer. 2015. Iris: Monoids and
invariants as an orthogonal basis for concurrent reasoning. POPL. DOI:
10.1145/2676726.2676980.

[@jung2018iris] Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Ales
Bizjak, Lars Birkedal, and Derek Dreyer. 2018. Iris from the ground up: A
modular foundation for higher-order concurrent separation logic. Journal of
Functional Programming. DOI: 10.1017/S0956796818000151.

[@turon2014gps] Aaron Turon, Viktor Vafeiadis, and Derek Dreyer. 2014. GPS:
Navigating weak memory with ghosts, protocols, and separation. OOPSLA. DOI:
10.1145/2660193.2660243.

[@jung2018rustbelt] Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, and
Derek Dreyer. 2018. RustBelt: Securing the foundations of the Rust programming
language. POPL. DOI: 10.1145/3158154.

[@milner1978theory] Robin Milner. 1978. A theory of type polymorphism in
programming. Journal of Computer and System Sciences.

[@FGJ] Atsushi Igarashi, Benjamin C. Pierce, and Philip Wadler. 2001.
Featherweight Java: A minimal core calculus for Java and GJ. ACM Transactions
on Programming Languages and Systems. DOI: 10.1145/503502.503505.
