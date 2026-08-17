import math
from fractions import Fraction
from sympy import primerange

from sieve_sequence import per_sequence_frontier_chart as p1
from sieve_sequence import frontier_comparison_stages_chart as p2
from sieve_sequence import fixed_lineage_hazard_chart as p3

print("== per_sequence_frontier_chart ==")
print("primes_upto(20):", p1.primes_upto(20))
print("primes_upto(2):", p1.primes_upto(2))
print("primes_upto(1):", p1.primes_upto(1))
try:
    print("primes_upto(0):", p1.primes_upto(0))
except IndexError as e:
    print("primes_upto(0) RAISES IndexError:", e)

stages = [
    {"head": 3, "survivors": list(range(3, 9, 2))},
    {"head": 5, "survivors": list(range(5, 26, 2))},
]
rows = p1.build_series(stages)
for r in rows:
    print("row:", r)

stages3 = [{"head": 3, "survivors": [3, 5, 7, 9, 11]}]
rows3 = p1.build_series(stages3)
print("g2 for [3,5,7,9,11] head=3:", rows3[0]["g2"])

print("dens check: 0.5 * (1-2/3) =", 0.5 * (1.0 - 2.0/3.0))
print("main stage1 expected: (25-5)*1/6 =", (25-5) * (1.0/6.0))

print("== frontier_comparison_stages_chart ==")
print("2.0/7 =", 2.0/7, " 2/7 =", 2/7, " equal:", 2.0/7 == 2/7)
print("2*(1+ln7)/7 =", 2.0*(1.0+math.log(7))/7)
print("target 0.8417 diff:", abs(2.0*(1.0+math.log(7))/7 - 0.8417))

ps = list(primerange(7, 98))
rb = [2.0/p for p in ps]
fb = [2.0*(1.0+math.log(p))/p for p in ps]
mono_r = all(b < a for a, b in zip(rb[:-1], rb[1:]))
mono_f = all(b < a for a, b in zip(fb[:-1], fb[1:]))
print("random mono strict decreasing:", mono_r)
print("frontier mono strict decreasing:", mono_f)
print("first/last random:", rb[0], rb[-1], "first/last frontier:", fb[0], fb[-1])

print("== fixed_lineage_hazard_chart ==")
print("math.log(3)=", math.log(3), " ->1.0986 diff", abs(math.log(3)-1.0986))
print("math.log(7)=", math.log(7), " ->1.9459 diff", abs(math.log(7)-1.9459))
print("math.log(29)=", math.log(29), " ->3.3673 diff", abs(math.log(29)-3.3673))
print("2*math.log(3)=", 2*math.log(3), " ->2.1972 diff", abs(2*math.log(3)-2.1972))
print("2*math.log(7)=", 2*math.log(7), " ->3.8918 diff", abs(2*math.log(7)-3.8918))

rs = list(primerange(3, 98))
ls = [math.log(r) for r in rs]
ts = [2*math.log(r) for r in rs]
print("log mono increasing:", all(b > a for a, b in zip(ls[:-1], ls[1:])))
print("2log mono increasing:", all(b > a for a, b in zip(ts[:-1], ts[1:])))

print("data_path(17):", p3.data_path(17))
print("endswith fixed-lineage-hazard-Q17.csv:", p3.data_path(17).endswith("fixed-lineage-hazard-Q17.csv"))