# Narration: primes and twins from one uniform rule

Companion to [the 35.53-second animation](output/uniform-prime-twins.mp4).
The [final plot](output/uniform-prime-twins.png) can remain visible while
reading the expanded explanation. The spoken script below is approximately
79 words; timings are approximate and allow natural phrasing. Expanded notes
are a separate reading guide, not additional speech to fit into the video.

## Timed spoken script

### 0:00–0:04 — Two linked curves

“One uniform rule builds two curves: primes above, twin starts below.”

### 0:04–0:08 — Apply the integer filters

“Each integer filters later multiples, lifting rejected candidates off the axis.”

### 0:08–0:10 — A composite step

“Composite filters change heights, not contacts.”

### 0:10–0:14 — Why the lower curve selects pairs

“Below, a contact survives only when both endpoint heights are zero.”

### 0:14–0:20 — Continue the uniform rule

“We keep adding every filter, including composites. Earlier prime contacts stay protected.”

### 0:20–0:28 — Contacts settle before the curves do

“Here, contacts settle after five. Later filters still change the curves, until both shapes stabilize.”

### 0:28–0:35.53 — Read the result

“Green marks primes. Gold marks twin starts: three, five, eleven, seventeen, and twenty-nine.”

## Expanded reading notes

### What the axes show

The horizontal position is the candidate number t. Vertical height is the
imaginary part of a complex-valued function. Zero height means the function
lies on the real axis; it does not mean the whole function equals zero.

Both panels show t from 2 through 31 with the same horizontal scale. The
vertical scales differ: read their labeled ticks rather than comparing the
apparent heights directly. Colored dots on the axis are surviving contacts;
faint red dots above it mark rejected integer inputs.

At intermediate stages the contacts are candidates. Calling the panels
“prime contacts” and “twin starts” describes their final result, not a claim
that every contact in the opening frames already has that status.

### Top panel: an integer's own divisor height

The upper curve is

```math
F_M(t)=t+i h_M(t).
```

M is the largest integer filter applied. At an integer n, h_M(n) counts
divisors d with 2<=d<=M and d<n. Every discovered proper divisor adds one
unit of height. After all relevant filters, a prime has height zero because
it has no divisor strictly between 1 and itself. A composite has positive
height. For example, 12 has height four from divisors 2, 3, 4, and 6.

The curves between integers come from continuous roots-of-unity detectors
and a sine-squared term. The sine term prevents noninteger contacts; it is
not a count of divisors at noninteger inputs.

### What adding a filter does

The filter indexed m acts only after m. Its activation is zero for t<=m,
increases continuously between m and m+1, then remains one. At later
integer multiples of m, it adds height. Its own integer m is protected.

The animation applies every integer 2, 3, 4, ..., 32. It does not need to find a
prime before defining the next step.

At filter 4, for example, later multiples of 4 gain more height. However,
filter 2 already rejected those integers, so no new integer contacts disappear.
The continuous curve still changes. The same redundancy holds for every
composite filter.

For a prime filter p, the first newly removed value in the upper panel is
p squared. At filter 5 that value is 25. The lower panel can lose a start
earlier: candidate 23 represents (23,25), so its second endpoint is struck.

### Bottom panel: both endpoints must survive

The lower curve is

```math
T_M(t)=t+i\bigl(h_M(t)+h_M(t+2)\bigr).
```

Its height adds the heights of the two endpoints. Both are nonnegative,
so their sum is zero exactly when both are zero. In the completed curve,
this means both endpoints are prime and differ by two.

A contact at 11 therefore represents the pair (11,13), not the two individual
positions 11 and 13 simultaneously displayed on the lower axis. A contact
at 13 would represent (13,15), which fails because 15 has positive height.

Subtraction would test equal heights and also admit two equally high
composites. Addition is what makes zero height require two surviving endpoints.

### Why the contacts stop changing after filter 5 here

The upper panel uses integers through 31. The lower panel also needs their
partners through 33. Every composite in this finite range has a prime divisor
among 2, 3, and 5, so those filters have already removed every false integer contact.

This is a statement about this displayed window, not about the entire
unbounded function. Later filters still reject new contacts farther away.
Within the window they can add height to already rejected values and change
the curve between integers.

### Why filter 32 gives the full continuous result in this window

The largest argument of either height function here is 33. Any filter m>=33
is inactive at all real inputs up to 33. Therefore, after filter 32, adding
more filters changes neither panel anywhere on its displayed interval.

The final mathematical curves are exact restrictions of the infinite
construction. The drawn curves are numerical samples of those functions;
they are not a claim of exact computer arithmetic between samples.

### What the final contacts mean

The upper contacts are the 11 primes
2,3,5,7,11,13,17,19,23,29,31.

The lower contacts are the five starts 3, 5, 11, 17, 29, representing
(3,5),(5,7),(11,13),(17,19),(29,31).

The demonstration shows how one uniform recurrence produces both sets on
a finite interval. It does not establish infinitely many twin primes or a
new bound on their spacing. Mathematical definitions and proofs are in
[Uniform Continuous Divisor Sieve](../../properties/sieve-sequence/uniform-continuous-divisor-sieve.md);
source and rendering commands are in the [animation README](README.md).
