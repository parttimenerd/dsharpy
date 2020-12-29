"""
Some statistics related helper functions, assume a normal distribution

Might contain dodgy statistics
"""
from typing import List

from scipy import stats, sqrt, var, mean, std, math


def mean_max(sample: List[float], alpha: float) -> float:
    """
    probability that the max is greater than the returned max is alpha

    see https://en.wikipedia.org/wiki/Normal_distribution#Confidence_intervals
    """
    alpha = alpha / 2
    return mean(sample) + stats.t.ppf(1 - alpha / 2, len(sample) - 1) * 1 / sqrt(len(sample)) * std(sample)


def std_max(sample: List[float], alpha: float) -> float:
    """
    probability that the std is greater than the returned max is alpha

    see https://en.wikipedia.org/wiki/Normal_distribution#Confidence_intervals
    """
    alpha = alpha / 2
    return sqrt((len(sample) - 1) * var(sample) / stats.chi2.ppf(alpha / 2, len(sample) - 1))


def probability_of_greater_max(sample: List[float], delta: float, ov_max: float, underlying_alpha: float = 0.05) -> float:
    m = mean_max(sample, underlying_alpha)
    s = std_max(sample, underlying_alpha)
    val = math.ceil(delta * max(sample))
    distr = stats.norm(loc=m, scale=s)
    ov = 1 - distr.cdf(0) - (1 - distr.cdf(ov_max))
    print(f"m = {m}, s={s}, val={val}, val0={ov}")
    return 1 - distr.cdf(val) / ov

if __name__ == '__main__':
    print(probability_of_greater_max([2,2,2,2,2,2,2,2,2,2], 1.1, 5))

