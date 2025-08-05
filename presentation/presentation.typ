#import "theme.typ": *

#import "@preview/numbly:0.1.0": numbly

#let target_date = datetime(year: 2025, month: 8, day: 7)
#show: lmu-theme.with(
  aspect-ratio: "16-9",
  footer: self => self.info.author,
  header-right: none,
  footer-progress: false,
  config-info(
    title: [Q - A Superposition Prover],
    subtitle: [Master Practical: Automated Theorem Provers],
    author: [Henrik Böving, Daniel Soukup],
    date: target_date.display("[day].[month].[year]"),
    institution: text(14pt, smallcaps("Ludwig-Maximilians-Universität München")),
    logo: image("lmu-sigillium.svg", height: 25%),
  ),
)
#show link: set text(fill: blue.darken(20%))

#title-slide()

= Q
- A superposition prover based on @braniac with:
  - TPTP FOF support
  - basic literal selection
  - a few simplification rules
  - efficient term orderings
  - efficient subsumption
  - graphic proof display
- Written in Rust
- Focus on getting a high performance implementation of the basic calculus

= Logic
We implement a basic first order logic with equality with the reductions:
- $p(x) arrow.r.squiggly p(x) = top$
- $not p(x) arrow.r.squiggly p(x) != top$
Crucially to avoid:
$ (forall x, y: x = y) and not p(a) "vs" (forall x, y: x = y) and p(a) != top $
we implement a 2-sorted logic with booleans and individuals

= Core Data Structures
- Logical:
  - Terms
  - Literals
  - Clauses
- Indexing:
  - Discrimination Trees
  - Feature Vector Index
  - Clause Queue

== Terms

#slide[
```rs
enum RawTerm {
    Var {
        id: VariableIdentifier,
        data: TermData,
    },
    App {
        id: FunctionIdentifier,
        args: Vec<Term>,
        data: TermData,
    },
}

type Term = HashConsed<RawTerm>;
```
][
Similar to @terms:
- fully shared with a term bank for meta data
  - $->$ small memory footprint
  - $->$ $O(1)$ equality with pointer equality
- RC for memory management
- pre-computed values:
  - hash for $O(1)$ hashing
    - $->$ $O(1)$ term caches
  - symbol/variable counts for weights
  - bloom filter for substitution
]
== Literals

#slide[
```rs
struct Literal {
    lhs: Term,
    rhs: Term,
    pol: Polarity,
    orient: Rc<OnceCell<Orient>>,
}
```
][
Similar to E's implementation:
- not (yet) fully shared
- identified up to symmetry:
  - equality check symmetries
  - hashing orders lhs/rhs by their pointer
- orientation gets lazily computed and cached:
  - in particular also carried over to copies
]

== Clauses
#slide[
```rs
struct Clause {
    id: ClauseId,
    info: ClauseInfo,
    literals: Vec<Literal>,
    selected: Rc<OnceCell<BitVec>>,
}
```
][
Similar to E's implementation:
- unique id to easily reference them:
  - could use pointers but annoying due to life times
- meta data for given clause selection
- selection gets lazily computed and cached
]

== Discrimination Tree
#slide[
```rs
enum DiscrTreeKey {
    Star,
    App {
        id: FunctionIdentifier,
        arity: usize,
    },
}

struct DiscriminationTree<V> {
    trie: Trie<DiscrTreeKey, V>,
}
```
][
Based on @handbooktwo:
- basic imperfect tree
- no optimization on the tree: never shows up in profiles
- no other index tried: profile almost always dominated by:
  - subsumption check
  - maximality check
]

== Feature Vector Index
#slide[
```rs
const FV_SIZE: usize = 16;

struct FeatureVector {
    vec: [usize; FV_SIZE],
}

struct FeatureVectorIndex {
    trie: Trie<usize, ClauseId>,
}
```
][
Based on @fvi:
- supports forward + backward subsumption
- uses the DRT-AC config:
  - counting pos/neg literals
  - counting a few symbols pos/neg
  - catch all for other symbols pos/neg
]

== Clause Queue
#slide[
```rs
const WEIGHTED_RATIO: usize = 10;

pub struct ClauseQueue {
    weighted: BinaryHeap<Clause>,
    fifo: VecDeque<Clause>,
    used: FxHashSet<ClauseId>,
    step: usize,
}
```
][
Based on @queue, uses `10SC11/FIFO-PI`:
- select ratio of 10:1 between:
  - symbol weight queue with weight 1 for functions and variables
  - FIFO queue
- both with bias for initial clauses
]

= Reasoning Engine
Basic DISCOUNT loop from @braniac:
+ select given clause
+ forward simplification
+ forward subsumption
+ backward subsumption
+ backward simplification
+ generating inferences
+ tautology check

== Term Ordering and Unification
Knuth Bendix Order:
- efficient version based on @kbo
- efficiently extended to literals like duper
- function symbol precende like in @braniac:
  - higher arity wins
  - same arity use arbitrary order from term bank

Unification:
- the naive algorithm from the lecture
- key component for enforcing well sortedness
- optimization: for ground terms just check equality (both $O(1)$)

== Generating Inferences
Uses the rules and side conditions from @braniac:
- two discrimination trees:
  - one with all subterms for paramodulating into
  - one with all equational literals for paramodulating from
    - pruned by orientation
- particular care in the maximality check as it often dominates the profiles
- configurable literal selection:
  - none
  - first negative literal
  - all positive literals and first negative maximal literal (@zipperposition default)

== Simplifications and Tautology Check
For simplification rules:
- rewriting in pos/neg literals (RN, RP)
  - cache per simplifier invocation but not globally
  - has a discrimination tree with all unit equational clauses
    pruned by orientation
- Deletion of duplicated literals (DD)
- Deletion of resolved literals (DR)

For tautology checking:
- Detecting reflexive literals (TD1)
- Detecting complementary literals (TD2)

== Subsumption
Heuristic based on @subsume:
- order literals to work likely harder ones earlier
- afterwards bruteforce using an efficient backtracking
  scheme like in @zipperposition
- uses a feature vector index for forward/backward substitution

= Performance
== Benchmarks
Ran TPTP Problems on privately owned hardware:
- CPU AMD Ryzen 7 9700X 8-Core Processor
- CPU Limit of 1-10 seconds depending on the benchmark
- Memory Limit of 1GB
- 16 Instances in parallel

CASC runs the problems sequentially on one CPU socket with a lot higher memory limit,
but it is not feasible for us while testing with private hardware.

// TODO: cite or delete
Initially used the pelletier problems, which are easy but are very broad.

== CASC
#grid(
  columns: 2,
  [#figure(
    image("cumulative_casc24.svg", width: 100%),
  ) <q_casc24>],
  [#figure(
    image("cumulative_casc29.svg", width: 100%),
  ) <q_casc29>]
)

== TPTPv9.0.0
#grid(
  columns: 2,
  [#figure(
    image("cumulative_theorems.svg", width: 100%),
  ) <q_theorems>],
  [#figure(
    image("cumulative_counter_satisfiable.svg", width: 100%),
  ) <q_counter_sat>]
)

== Comparison with E and Zipperposition
#grid(
  columns: 2,
  [#figure(
    image("comp_casc24.svg", width: 100%),
  ) <comparison_casc24>],
  [#figure(
    image("comp_casc29.svg", width: 100%),
  ) <comparison_casc29>]
)

#grid(
  columns: 2,
  [#figure(
    image("comp_theorems.svg", width: 100%),
  ) <comparison_theorems>],
  [#figure(
    image("comp_counter_satisfiable.svg", width: 100%),
  ) <comparison_counter_sat>]
)

#show: appendix

= Bibliography
#bibliography("literature.bib", title: none)
