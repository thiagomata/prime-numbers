"""Pure, no-I/O library for the phase-transition curves in
articles/draft/draft-adversariality-phase-transition-2-gap-companions.md.

These are theoretical asymptotic curves, not anchored to one real measured
lineage chain the way four_lines.py / spacing.py are. That means they can be
evaluated at arbitrarily large Q with no ceiling from real data -- but for a
fixed relative-hazard factor w (the article's Property III: "no finite
constant multiple of random is fatal"), the divergence to infinity can stay
numerically invisible until Q is astronomically large, because
Q^2 must overtake (ln Q)^(2w), and for large w that crossover point is far
beyond ordinary float range. All window-occupancy functions here therefore
return log10 of the target quantity, computed directly from log10(Q) so Q
itself never needs to be materialized as a float.

The head-recurrence functions return actual (non-log) probabilities, because
those are summed over real, enumerable primes up to a feasible bound
(~10^6-10^7) rather than evaluated at astronomical Q -- the log-growth
family's phase transition is polynomial-rate in Q, not double-logarithmic,
so it is visible well within that range (see the CLI and
tests/test_phase_transition.py for the numeric confirmation).
"""

from __future__ import annotations

import math


def log10_window_occupancy_fixed_w(log10_Q: float, w: float) -> float:
    """log10(lambda_w(Q)), lambda_w(Q) ~ Q^2 / (ln Q)^(2w).

    Expected square-safe-window occupancy under a fixed relative-hazard
    factor w (draft Property III, section 5.1). Proved to diverge to
    infinity for every finite w -- the point of this function is to make
    that divergence checkable even where it is numerically extremely slow
    to appear.
    """
    ln_Q = log10_Q * math.log(10)
    return 2.0 * log10_Q - 2.0 * w * math.log10(ln_Q)


def log10_window_occupancy_log_growth(log10_Q: float, c: float) -> float:
    """log10(lambda_c(Q)), lambda_c(Q) ~ Q^(2-2c) / (ln Q)^2.

    Expected square-safe-window occupancy for w_r = 1 + c*log(r) (draft
    Property IV, section 5.2). Diverges for c<1, tends to 0 for c>=1.
    c=0 reduces to exactly log10_window_occupancy_fixed_w(log10_Q, 1).
    """
    ln_Q = log10_Q * math.log(10)
    return (2.0 - 2.0 * c) * log10_Q - 2.0 * math.log10(ln_Q)


def log10_window_occupancy_constant_share(log10_Q: float, alpha: float) -> float:
    """log10(lambda(Q)) under a fixed positive per-filter adversarial share
    alpha (draft section 7): lambda ~ Q^2/(ln Q)^2 * (1-alpha)^pi(Q), using
    the asymptotic pi(Q) ~ Q/ln(Q) (since Q is astronomical here, not an
    actual integer to factor -- exact pi(Q) is infeasible and unnecessary
    for this asymptotic comparison).

    Proved locally fatal for every alpha>0 (draft section 7): this function
    is strictly decreasing in log10_Q once Q is large enough, unlike every
    fixed-w or subcritical log-growth curve above.
    """
    ln_Q = log10_Q * math.log(10)
    pi_Q = (10.0 ** log10_Q) / ln_Q if log10_Q < 300 else None
    window_part = 2.0 * log10_Q - 2.0 * math.log10(ln_Q)
    if pi_Q is not None:
        decay_part = pi_Q * math.log10(1.0 - alpha)
    else:
        # log10(Q) too large to materialize Q as a float (10**300+); use
        # log10(pi(Q)) = log10_Q - log10(ln_Q) directly instead.
        log10_pi_Q = log10_Q - math.log10(ln_Q)
        decay_part = (10.0 ** log10_pi_Q) * math.log10(1.0 - alpha)
    return window_part + decay_part


def head_probability_log_growth(Q: float, c: float) -> float:
    """Pr(H_Q) ~ 1/(Q^(2c) (ln Q)^2) for w_r = 1 + c*log(r) (draft section
    5.2). Q is a real, feasibly-sized prime here (not astronomical), since
    this is meant to be summed over actual enumerated primes.
    """
    return 1.0 / ((Q ** (2.0 * c)) * (math.log(Q) ** 2))
