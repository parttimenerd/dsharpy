# source: https://github.com/dfremont/maxcount
#
# MaxCount 1.0.0
# An approximate Max#SAT solver
# Written by Daniel Fremont and Markus Rabe
# This algorithm is explained in the paper "Maximum Model Counting"
# by Daniel J. Fremont, Markus N. Rabe, and Sanjit A. Seshia, AAAI 2017
#
# modified by Johannes Bechberger to work directly with dsharpy instead of scalmc
#   only uses hashing mode
#   only uses k = 0
#   does not yet compute with the printed accuracy


import sys
import os
import math
import random
from dataclasses import dataclass
from pathlib import Path

import time
import argparse

### parse command-line arguments
from typing import Any

from dsharpy.counter import State, Config
from dsharpy.formula import DCNF
from dsharpy.util import random_seed

"""
@dataclass
class Args:

    inputFilename: str
    runIndex: int = 0
    seed: int = 0
    verbosity: int = 2
"""


def run(args: Any) -> float:

    inputFilename = args.inputFilename
    if ' ' in inputFilename:
        raise Exception('the input file cannot have spaces in its name')

    seed = args.seed
    random_seed(seed)
    runIndex = args.runIndex
    verbosity = args.verbosity

    numSamples = args.samples
    kappa = args.samplingKappa
    useMultisampling = args.multisample
    if numSamples < 1:
        raise Exception('number of samples must be positive')
    if kappa <= 0 or kappa >= 1:
        raise Exception('samplingKappa must be strictly between 0 and 1')

    upperBoundConfidence = args.upperBoundConfidence
    countConfidence = args.lowerBoundConfidence
    if upperBoundConfidence <= 0 or upperBoundConfidence >= 1:
        raise Exception('upperBoundConfidence must be strictly between 0 and 1')
    if countConfidence <= 0 or countConfidence >= 1:
        raise Exception('lowerBoundConfidence must be strictly between 0 and 1')
    if upperBoundConfidence >= countConfidence:
        # the correctness of the upper bound depends on that of the count, so countConfidence
        # (which is the confidence of the lower bound) must be greater than upperBoundConfidence
        # raise Exception('lowerBoundConfidence must be strictly greater than upperBoundConfidence')
        countConfidence = 1 - ((1 - upperBoundConfidence) / 2)  # heuristic

    countEpsilon = args.countingTolerance
    if countEpsilon <= 0:
        raise Exception('countingTolerance must be positive')

    useRefinement = args.refine
    refinementEpsilon = args.refinementTolerance

    ### initialization

    startTime = time.time()


    # function for printing only at a certain level of verbosity
    def printV(verbosityLevel, text, withNewline=True):
        if verbosity >= verbosityLevel:
            if withNewline:
                print(text)
            else:
                sys.stdout.write(text)


    random.seed(seed)
    printV(2, 'c Using random seed %d, runIndex %d' % (seed, runIndex))

    # temporary file names
    outputFilename = inputFilename + '.' + str(runIndex) + '.out'
    onefoldFilename = inputFilename + '.' + str(runIndex) + '.1fold'
    countFilename = inputFilename + '.' + str(runIndex) + '.count'
    cuspLogFilename = inputFilename + '.' + str(runIndex) + '.log'

    ## sampling parameters

    # the formula for sampleEpsilon depends on the choices of
    # samplingPivotAC and samplingTApproxMC - see the UniGen2 paper (TACAS 2015)
    # samplingPivotAC = 73
    # samplingTApproxMC = 67
    # kappa = 0.638
    # sampleEpsilon = ((1 + kappa) * (7.44 + (0.392 / ((1 - kappa) * (1 - kappa))))) - 1
    sampleEpsilon = ((1 + kappa) * (8.227 + (0.453 / ((1 - kappa) * (1 - kappa))))) - 1

    # multisampling will generate more samples, but not correspondingly improve the
    # theoretical guarantees (currently)
    if useMultisampling:
        uniGenPivot = math.ceil(4.03 * (1 + (1 / kappa)) * (1 + (1 / kappa)))
        uniGenLoThresh = int(uniGenPivot / (1.41 * (1 + kappa)))
        uniGenNumSamples = numSamples * uniGenLoThresh
    else:
        uniGenNumSamples = numSamples

    ## counting parameters

    refinementFailureProb = (1.0 - countConfidence) / (uniGenNumSamples + 1)  # heuristic
    refinementConfidence = 1.0 - refinementFailureProb

    if useRefinement:
        perSampleCountingFailure = ((1.0 - countConfidence) - refinementFailureProb) / uniGenNumSamples
        if perSampleCountingFailure <= 0:
            raise Exception('refinementConfidence must be greater than countConfidence')
    else:
        perSampleCountingFailure = (1.0 - countConfidence) / uniGenNumSamples
    perSampleCountingConfidence = 1 - perSampleCountingFailure

    monteCarloDensityConfidence = 1 - (perSampleCountingFailure / 2)  # heuristic
    if monteCarloDensityConfidence <= perSampleCountingConfidence:
        raise Exception('monteCarloDensityConfidence must be strictly greater than perSampleCountingConfidence')

    # some versions of Python lack math.log2
    try:
        log2 = math.log2
    except AttributeError:
        log2 = lambda x: math.log(x, 2)

    # For greater reproducibility, we don't use any of the derived random number
    # generation functions in Python (they've changed before, e.g. in 3.2).
    randbool = lambda: random.random() < 0.5

    ### parse formula and extract maximization/counting variables

    printV(2, 'c Parsing formula...')

    maxVars = []
    seenMaxVars = set()
    countingVars = set()
    with open(inputFilename, 'r') as inputFile:
        for (lineNumber, line) in enumerate(inputFile, start=1):
            if line[:6] == 'c max ':
                fields = line.split()[2:]
                if fields[-1] != '0':
                    raise Exception('Malformed maximization variable comment on line ' + str(lineNumber))
                try:
                    for field in fields[:-1]:
                        var = int(field)
                        if var not in seenMaxVars:
                            maxVars.append(var)
                            seenMaxVars.add(var)
                except ValueError:
                    raise Exception('Non-integer maximization variable on line ' + str(lineNumber))
            elif line[:6] == 'c ind ':
                fields = line.split()[2:]
                if fields[-1] != '0':
                    raise Exception('Malformed counting variable comment on line ' + str(lineNumber))
                try:
                    for field in fields[:-1]:
                        countingVars.add(int(field))
                except ValueError:
                    raise Exception('Non-integer counting variable on line ' + str(lineNumber))
    numCountingVars = len(countingVars)

    printV(2, 'c Formula has %d maximization and %d counting variables' % (len(maxVars), numCountingVars))

    ### sample from assignments to maximization variables

    printV(2, 'c Generating %d independent samples from 0-fold self-composition' % (numSamples))

    if useMultisampling:
        printV(2, 'c Using multisampling: %d total samples' % uniGenNumSamples)

    samples = set()
    # k == 0:  # sample uniformly from assignments to maximization variables
    for i in range(numSamples):
        sample = []
        for var in maxVars:
            if randbool():
                sample.append(var)
            else:
                sample.append(-var)
        samples.add(tuple(sample))

    printV(2, 'c Obtained %d distinct assignments to maximization variables' % len(samples))

    if len(samples) == 0:
        printV(0, 'c Formula is UNSAT')
        printV(0, 'c Estimated max-count: 0 x 2^0')
        printV(1, 'c Max-count is <= 0 x 2^0 with probability >= 1')
        printV(1, 'c Max-count is >= 0 x 2^0 with probability >= 1')
        printV(2, 'c Total runtime %d s' % (time.time() - startTime))
        sys.exit(0)

    ### count solutions for each sample

    def countSampleWithHashing(sample, epsilon=countEpsilon, confidence=perSampleCountingConfidence):
        pivotAC = int(math.ceil(9.84 * (1 + (epsilon / (1.0 + epsilon))) * (1 + (1.0 / epsilon)) * (1 + (1.0 / epsilon))))
        tApproxMC = int(math.ceil(17 * log2(3.0 / (1 - confidence))))

        countCommand = str(Path(__file__).parent.parent.parent) + '/util/approxmc2 --cuspLogFile=' + cuspLogFilename
        countCommand += ' --random=' + str(seed)
        #countCommand += ' --pivotAC=' + str(pivotAC)
        countCommand += ' --tApproxMC=' + str(tApproxMC)
        countCommand += ' ' + countFilename + ' > ' + outputFilename
        # assign maximization variables by adding unit clauses
        os.system('cp ' + onefoldFilename + ' ' + countFilename)
        with open(countFilename, 'w') as countFile:
            countFile.write("\n".join([l for l in Path(countFilename).read_text().split("\n") if len(l) > 0] + [f'{x} 0' for x in sample]))
        # count resulting formula
        #os.system(countCommand)

        ret = State.from_dcnf(DCNF.load(Path(countFilename)), Config(epsilon=epsilon, delta=1 - upperBoundConfidence / actualCountConfidence)).compute_loop(tApproxMC)
        if ret == -1:
            raise Exception("Unsatisfiable")
        sampleExp = math.floor(math.log2(ret))
        sampleMant = ret / (2 ** sampleExp)
        return (sampleMant, sampleExp, False)

    def countSample(sample, label, confidence=perSampleCountingConfidence, epsilon=countEpsilon):

        printV(2, 'c Counting %s with hashing... ' % label, False)
        sys.stdout.flush()

        (sampleMant, sampleExp, sampleExact) = countSampleWithHashing(sample, epsilon=epsilon, confidence=confidence)
        printV(2, '%.3f x 2^%d' % (sampleMant, sampleExp))
        return (sampleMant, sampleExp, sampleExact, 1 + epsilon, confidence)

    printV(2, 'c Using hashing tolerance (1+%g) and confidence %g' % (countEpsilon, perSampleCountingConfidence))
    timepoint = time.time()

    maxMant = -1
    maxExp = -1
    maxSample = None
    maxExact = False  # whether the count for maxSample is exact
    maxMultError = -1
    actualCountConfidence = 1
    worstMultError = 1
    for (index, sample) in enumerate(samples):
        label = 'witness ' + str(index + 1)
        (sampleMant, sampleExp, sampleExact, sampleMultError, sampleConfidence) = countSample(sample, label)

        if not sampleExact:
            actualCountConfidence *= sampleConfidence
        if sampleMultError > worstMultError:
            worstMultError = sampleMultError

        # see if count is larger than the best so far
        if sampleExp > maxExp or (sampleExp == maxExp and sampleMant > maxMant):
            maxMant = sampleMant
            maxExp = sampleExp
            maxSample = sample
            maxExact = sampleExact
            maxMultError = sampleMultError

    if actualCountConfidence < countConfidence:
        raise Exception('count confidence calculation corrupted')

    printV(2, 'c Counting completed in %d s' % (time.time() - timepoint))

    printV(2, 'c Witness with largest estimated count:')
    printV(0, 'v ', False)
    for literal in maxSample:
        printV(0, str(literal) + ' ', False)
    printV(0, '0')

    if maxExact:
        printV(2, 'c Estimated count for this witness is exact')

    ### optionally refine count for the best sample

    refinedMant = maxMant
    refinedExp = maxExp
    refinedExact = maxExact
    refinedMultError = maxMultError
    refinedConfidence = actualCountConfidence
    if useRefinement and not maxExact:
        printV(2, 'c Using hashing tolerance (1+%g) and confidence %g' % (refinementEpsilon, refinementConfidence))

        timepoint = time.time()

        label = 'witness'
        (newRefinedMant, newRefinedExp, newRefinedExact, newRefinedMultError, newRefinedConfidence) = countSample(sample,
                                                                                                                  label,
                                                                                                                  confidence=refinementConfidence,
                                                                                                                  epsilon=refinementEpsilon)
        printV(2, 'c Refinement completed in %d s' % (time.time() - timepoint))
        printV(2, 'c Refined witness count: %g x 2^%d' % (newRefinedMant, newRefinedExp))

        if newRefinedExp > refinedExp or (newRefinedExp == refinedExp and newRefinedMant >= refinedMant):
            refinedMant = newRefinedMant
            refinedExp = newRefinedExp
            refinedExact = newRefinedExact
            refinedMultError = newRefinedMultError
            refinedConfidence = actualCountConfidence + newRefinedConfidence - 1

    ### output max-count estimate and bounds

    # compute smallest upperMultError such that with at least the desired confidence,
    # all estimated counts are within (1+countEpsilon) error and at least one sample
    # has count at most a factor of upperMultError less than the maximum
    useTrivialUpperBound = False
    requiredConfidence = upperBoundConfidence / actualCountConfidence
    requiredDelta = 1 - requiredConfidence
    f = (1 - (requiredDelta ** (1.0 / numSamples))) * (1 + sampleEpsilon)
    if f >= 1:  # cannot do better than trivial bound
        useTrivialUpperBound = True
    else:
        # compute probability of getting the maximum by sheer luck
        mp = 2.0 ** -len(maxVars)
        mp = 1 - ((1 - mp) ** numSamples)
        if mp >= requiredConfidence:
            upperMultError = 1
        else:
            useTrivialUpperBound = True
    ## compute upper bound

    sampleBoundTrivial = False
    if not useTrivialUpperBound:
        upperBoundMant = maxMant * upperMultError
        if not maxExact:
            upperBoundMant *= maxMultError
        upperBoundExp = maxExp

        if log2(maxMultError) + log2(worstMultError) + log2(upperMultError) >= numCountingVars:
            sampleBoundTrivial = True

    clampedMaxMant = maxMant
    clampedMaxExp = maxExp
    if maxExp >= numCountingVars:
        useTrivialUpperBound = True
        clampedMaxMant = 1
        clampedMaxExp = numCountingVars

    if useTrivialUpperBound or sampleBoundTrivial:
        diff = numCountingVars - clampedMaxExp
        if diff > 1000:
            quality = 0
        else:
            quality = (clampedMaxMant / (2.0 ** (numCountingVars - clampedMaxExp))) / maxMultError
        printV(2, 'c Witness quality (exact count / max-count) >= %g with probability >= %g' % (
        quality, actualCountConfidence))
    else:
        quality = 1 / (maxMultError * worstMultError * upperMultError)
        printV(2,
               'c Witness quality (exact count / max-count) >= %g with probability >= %g' % (quality, upperBoundConfidence))

    printV(0, 'c Estimated max-count: %g x 2^%d' % (clampedMaxMant, clampedMaxExp))

    if useTrivialUpperBound or (upperBoundMant > 0 and log2(upperBoundMant) + upperBoundExp >= numCountingVars):
        printV(1, 'c Max-count is <= 1 x 2^%d with probability >= 1 (trivial bound)' % numCountingVars)
    else:
        while upperBoundMant >= 2:
            upperBoundMant /= 2
            upperBoundExp += 1
        printV(1,
               'c Max-count is <= %g x 2^%d with probability >= %g' % (upperBoundMant, upperBoundExp, upperBoundConfidence))

    ## compute lower bound

    lowerBoundMant = refinedMant
    if refinedExact:
        lowerBoundConfidence = 1
    else:
        lowerBoundConfidence = refinedConfidence
        lowerBoundMant /= refinedMultError
    lowerBoundExp = refinedExp
    while lowerBoundMant > 0 and lowerBoundMant < 1:
        lowerBoundMant *= 2
        lowerBoundExp -= 1

    if lowerBoundMant <= 0:
        printV(1, 'c Max-count is >= 0 x 2^0 with probability >= 1 (trivial bound)')
    else:
        printV(1,
               'c Max-count is >= %g x 2^%d with probability >= %g' % (lowerBoundMant, lowerBoundExp, lowerBoundConfidence))

    printV(2, 'c Total runtime %d s' % (time.time() - startTime))


def cli():
    parser = argparse.ArgumentParser(description='Approximately solve a Max#SAT problem with dependencies.',
                                     usage='%(prog)s [-h] [options] formula',
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)

    ## required arguments

    parser.add_argument('inputFilename', help='Max#SAT problem to solve, in extended DIMACS format', metavar='formula')

    ## optional arguments

    # general
    parser.add_argument('--seed', help='random seed to use', metavar='s', type=int, default=0)
    parser.add_argument('--runIndex',
                        help='number included in temporary file names (useful for running multiple instances simultaneously)',
                        metavar='r', type=int, default=0)
    parser.add_argument('--verbosity',
                        help='information to output: 0 = max-count estimate and witness; 1 = also max-count bounds; 2 = everything',
                        metavar='level', type=int, choices=[0, 1, 2], default=2)

    # sampling
    parser.add_argument('--samples', help='number of samples to generate from self-composition', metavar='n', type=int,
                        default=20)
    parser.add_argument('--samplingKappa',
                        help='kappa parameter for UniGen2 (determines sampling tolerance; kappa=0.5782 corresponds to epsilon=16)',
                        metavar='kappa', type=float, default=0.5782)
    parser.add_argument('--multisample',
                        help='return multiple samples from each UniGen2 call; may yield better results than correspondingly increasing --samples, but the tool does not currently take full advantage of this',
                        action='store_true')

    # counting
    parser.add_argument('--countingTolerance', help='counting tolerance', metavar='epsilon', type=float, default=1)
    parser.add_argument('--upperBoundConfidence', help='minimum confidence for upper bound', metavar='uconf',
                        type=float,
                        default=0.6)
    parser.add_argument('--lowerBoundConfidence', help='minimum confidence for lower bound', metavar='lconf',
                        type=float,
                        default=0.8)
    parser.add_argument('--monteCarloSamples', help='number of Monte Carlo samples for counting', metavar='n', type=int,
                        default=2000)
    parser.add_argument('--enumerationThreshold', help='maximum number of solutions to enumerate for exact counting',
                        metavar='n', type=int, default=256)

    # refinement (disabled by default)
    parser.add_argument('--refine', help='refine count of best sample obtained', action='store_true')
    parser.add_argument('--refinementTolerance', help='counting tolerance for refinement', metavar='epsilon',
                        type=float,
                        default=0.4142)
    parser.add_argument('--refinementMCSamples', help='number of Monte Carlo samples for refinement', metavar='n',
                        type=int,
                        default=20000)
    parser.add_argument('--refinementEnumThreshold',
                        help='maximum number of solutions to enumerate for exact refinement',
                        metavar='n', type=int, default=1024)

    ## parse and validate arguments

    args = parser.parse_args()

    run(args)
