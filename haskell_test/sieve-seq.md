# Sieve Sequences

A wheel-based prime number sieve using sequences of steps to generate candidates.

## Core Concept

Generate prime numbers by maintaining a sequence of **steps** that, when added cyclically to an initial value, produces numbers that are never multiples of a set of primes.

The key insight is that we can represent a candidate list as a **cycle integral**:

```
Avoid(D) = CycleIntegral(Gaps(D), init)
```

Where `D` is a set of forbidden divisors, `Gaps(D)` is the cyclic list of distances between valid residues modulo `lcm(D)`, and `init` is the starting value.

## Mathematical Definition

### The Sequence Hierarchy

We define a hierarchy of sequences `S_n` where each level filters multiples of the next prime:

```
S_0 = [2, 3, 4, 5, 6, 7, 8, ...]

p_0 = head(S_0) = 2
S_1 = [x ∈ S_0 | x > p_0 and x % p_0 != 0] = [3, 5, 7, 9, 11, ...]

p_1 = head(S_1) = 3
S_2 = [x ∈ S_1 | x > p_1 and x % p_1 != 0] = [5, 7, 11, 13, 17, ...]

p_2 = head(S_2) = 5
S_3 = [7, 11, 13, 17, 19, 23, 29, 31, ...]
```

The heads `p_0, p_1, p_2, ...` are exactly the primes.

### Wheel Modulo Representation

Each `S_n` can be represented as a wheel:

```
M_n = ∏_{j=0}^{n} p_j           -- product of first n+1 primes
R_n = {r ∈ [0, M_n-1] | ∀j ≤ n, r % p_j != 0}  -- valid residues
G_n = gaps(R_n)                 -- differences between sorted residues
S_n = CycleIntegral(G_n, init_n)
```

**Examples:**

| n | M_n | R_n | G_n |
|---|-----|-----|-----|
| 0 | 2 | [1] | [2] |
| 1 | 6 | [1, 5] | [4, 2] |
| 2 | 30 | [1, 7, 11, 13, 17, 19, 23, 29] | [6, 4, 2, 4, 2, 4, 6, 2] |

### Transition: S_n → S_{n+1}

Given `S_n = CycleIntegral(G_n, init_n)`, we build `S_{n+1}` by:

1. Let `p_n = head(S_n)` be the next prime
2. Filter `S_n` to remove multiples of `p_n`
3. Derive the new gap cycle `G_{n+1}` from the filtered list
4. Set `init_{n+1} = p_{n+1}` (next prime)

```
G_{n+1} = gaps({x % M_{n+1} | x ∈ S_n, x % p_n != 0})
M_{n+1} = M_n × p_n
S_{n+1} = CycleIntegral(G_{n+1}, p_{n+1})
```

**Proof shape:** The key invariant is:

```
x ∈ S_{n+1} ⟺ x ∈ S_n and x > p_n and x % p_n != 0
           ⟺ x > p_n and ∀k ≤ n, x % p_k != 0
```

By induction, the heads `p_n` are exactly the sieve primes.

## Data Model

### Sequence (`Seq`)

```haskell
data Seq = Seq {
    values    :: [Integer],  -- Current position in the wheel
    steps     :: [Integer],  -- Step pattern (wheel spokes)
    seqLength :: Integer     -- Length of the step pattern
}
```

### First Sequence

```haskell
firstSequence = Seq {
    values = [3, 2],
    steps  = [2],
    seqLength = 2
}
```

- Initial value: `3` (first prime after 2)
- First step pattern: `[2]`
- Generated sequence: `3, 5, 7, 9, 11, ...` (all odd numbers)

## Algorithm

### Step 1: Generate Candidates

Given a sequence, generate numbers by accumulating steps:

```haskell
preview seq count = reverse(values) ++ previewLoop count (cycle steps) acc
  where
    acc = head(values)
    previewLoop 0 _ _ = []
    previewLoop n (s:steps) acc = (acc + s) : previewLoop (n-1) steps (acc + s)
```

### Step 2: Build Next Sequence

When we reach the first number **not yet proven composite**, that becomes the next prime. We then create a new sequence that filters out all multiples of this prime.

```haskell
next seq = Seq {
    values = (nextValue : currentValues),
    steps  = getNextSequence rotatedSteps currentValue nextValue nextSeqLength,
    seqLength = currentSeqLength * currentValue
}
```

Where:
- `currentValue` = smallest number in current sequence (potential next prime)
- `nextValue` = `currentValue + head(steps)` (first candidate after currentValue)
- `getNextSequence` constructs steps that skip all multiples of `currentValue`

### Step 3: The Sequence Loop

The core of step construction:

```haskell
sequenceLoop :: [Integer] -> Integer -> Integer -> Integer -> [Integer]
sequenceLoop []       _  _  _ = []
sequenceLoop (x:y:xs) n  acc l
    | acc + x == l        = [x]
    | acc + x + y == l    = [x + y]
    | imod (acc + x) n == 0 = [x + y] ++ sequenceLoop xs n (acc + x + y) l
    | otherwise           = [x] ++ sequenceLoop (y:xs) n (acc + x) l
```

**Key invariant**: `(sum of steps) % currentPrime == 0`

This ensures the step pattern can be cycled without hitting multiples.

## Key Properties

### Invariant 1: Non-Multiples

For a sequence with step pattern `S` and initial value `v`:

```
forall x in integral(S, v): x % p != 0 for all primes p in set
```

### Invariant 2: Step Sum Divisibility

```
sum(S) % p == 0 for all primes p in set
```

### Invariant 3: Sorted Output

```
integral(S, v) is strictly increasing
```

## Dafny Proofs

The Dafny verification in `dafny/sequence.dfy` proves:

### `modOfIntegralIsCycleFull`

If the sum of steps is divisible by prime `p`, then the modular residues of the integral sequence form a cycle.

**Requires:**
- `sum(steps) % p == 0`
- `steps` is non-empty and non-zero

**Ensures:**
- `modIntegralList` is a cycle (repeats every `|steps|` elements)
- If `modIntegralList` has no zeros, neither does its cycle

### `makingAListNotMultipleOfNextValue`

The inductive step: given a sequence filtered from primes `P`, we can construct a new sequence filtered from `P ∪ {nextPrime}`.

**Key condition:**
```
(nextInitial % nextPrime) != 0
```

This is necessary because `nextInitial = currentValue + firstStep`, and we need it to not be divisible by `nextPrime`.

## Example Execution

### Initial State

```
values = [3, 2]
steps  = [2]
```

### Preview

```
3, 5, 7, 9, 11, 13, 15, 17, ...
```

### Finding Next Prime

`3` is prime (not divisible by 2). Build next sequence:

1. Filter odd numbers to remove multiples of 3
2. New step pattern: `[2, 4]` (difference between consecutive non-multiples of 3)
3. New sequence value: `5` (next candidate)

### Second Sequence

```
values = [5, 3, 2]
steps  = [2, 4]
```

### Preview

```
5, 7, 11, 13, 17, 19, 23, 25, 29, ...
```

Notice `9, 15, 21, 25, 27, 33, 35, 39...` (multiples of 3 or 5) are skipped.

### Finding Next Prime

`5` is prime. Build next sequence...

## Complexity

- **Space**: O(k) where k is the number of primes found (stores step patterns)
- **Time**: Each number is examined once per sequence transition
- **Memory**: Each sequence stores `O(n)` steps where n is the number of primes

## References

- [Haskell Implementation](./haskell/primeseq/src/Sequence.hs)
- [Dafny Proofs](./dafny/sequence.dfy)
- Helper modules (Dafny):
  - `list.dfy` - List properties (sorted, sum, shift)
  - `modDiv.dfy` - Modular arithmetic
  - `cycle.dfy` - Cycle behavior
  - `integral.dfy` - Cumulative sums
  - `derivative.dfy` - Step differences
  - `multiple.dfy` - Multiple filtering