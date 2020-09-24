# prime-numbers

A small study about prime numbers using different approaches and programming languages.

## Sequences and Steps

This study intends to compare different ways to calculate prime numbers.
Specially related to evaluate one (possible new?) way using sequences and steps.

### Avoiding pair numbers

One very common improvement to the classic prime search is avoiding evaluate pair numbers different of the number 2.
This is clearly because after 2, all pair numbers are not prime and we should avoid wasting time evaluating them.

So, if we look to the numbers evaluated by this solution, we would see something like:

```javascript
[2,3,5,7,9,11,13,15,17,...]
```

One different way to see this is looking to the distance between the numbers after separating the previous found primes.
We are calling this distance between the numbers that should be evaluated as "steps", the previous values as "values" and the struct with the "values" and "steps" as "Sequence".

```javascript
Sequence {
    values: [2,3]
    steps: [2,2,2,2,2....]
}
```

Basically, after loading all the previous found values, we keep our list applying the steps.
As you can see, the steps in this particular list are always the same.
So, considering that this is an cycle list, that is, after loading the last element we are going to return to the first, we can rewrite our sequence in this format:

```javascript
Sequence s2 {
    values: [2,3]
    steps: [2]
}
```

## Creating a new sequence based on the previous

The question that started this study is if is possible to create more complex Sequences that would avoid also multiples of other prime numbers.
More importantly, if is possible to create a sequence that avoids the next prime number based on the current sequence.

Let's consider the sequence that should avoid the multiples of 2 and 3. That Sequence should be like this:
```javascript
Sequence s3 {
    values: [2,3,5]
    steps: [2,4]
}
```
In other words, after loading the values ``[2,3,5]`` the sequence should keep following adding the values ``[2,4]`` to avoid the multiples of 2 and 3.
We can see that the result of that operation should be:
```javascript
[2,3,5,7,11,13,17,19,23,...]
```

So, how can we create this new sequence based on the previous on? How can we create the `nextSequence` method to work as described as follows?

```javascript
// in this particular case
val Sequence s3 = s2.nextSequence()
// in the general case
val Sequence nextSequence = currentSequence.nextSequence()
```
First, we had to find the next value. Then, we have to create the new steps.

### Current Last value
The goal is create a new list that still avoids the pair numbers, multiples of 2, but that also avoids the numbers that are multipes of 3. So, we are going to call the 3 as our current last value.
```javascript
val currentLastValue  = max(currentSequence.values)
```

### Next value

Loading the next step is a trivial operation. Since we are avoiding all the numbers that a multiples from the previous values, the next number in the Sequence should be our next value.

```javascript
val nextValue = max(currentSequence.values) + currentSequence.step[0] = 3 + 2 = 5
```

### Next steps

To define the next step we must first multiple our list by the next value. That is, in this particular case, that we are  repeating 3 times the previous one.

```javascript
currentSequence.steps.repeat(currentLastValue) = [2,2,2]
 ```

We can see that the sum of the values of this new list of steps (6 in this case) will be multiple by both values 2 and 3. That is important because that ensures that when we cycle the list, the mod result will be the same.

Then, we create a accumulator that starts with the next value (5) and walks throught our new list. If some element is multiple of the current value it should be combined with the next one.

```javascript
input {nextValue:5,toEvaluate:[2,2,2]}
{ accumulator: 5, nextSteps: []. toEvaluate: [2,2,2], mustCombine: false }
{ accumulator: 7, nextSteps: [2]. toEvaluate: [2,2], mustCombine: false }
{ accumulator: 9, nextSteps: [2,2]. toEvaluate: [2], mustCombine: true }
{ accumulator: 11, nextSteps: [2,4]. toEvaluate: [], mustCombine: false }
output [2,4]
```

So, it is possible create a new Sequence based on the previous one.

## Implemementation

You can find an implementation of this algorithm in this project using Javascript, TypesScript and Haskell in this project. Also, we are working in ways to compare it the performance of this solution.

To improve performance and make a good use of the Haskell lazy evaluation, the implementation code on Haskell had some changes. We will add more comments around each implementation as soon as possible. 

# Sequences

## S1 - All natural numbers, starting at 2

Using the presented definiton, we can define the first sequence as
```javascript
val s1 = Sequence {
    values: [2],
    steps: [1]
}
s1.preview(100) = [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102]
```
That should include all integer numbers bigger than 1.

## S2 - Non multiples of 2, starting at 3
```javascript
val s2 = Sequence {
    values = [3,2], 
    steps = [2]
}
s2.preview(100) = [2,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99,101,103,105,107,109,111,113,115,117,119,121,123,125,127,129,131,133,135,137,139,141,143,145,147,149,151,153,155,157,159,161,163,165,167,169,171,173,175,177,179,181,183,185,187,189,191,193,195,197,199,201,203]

```

## S3 - Non multiples of 2 and 3, starting at 5
```javascript
val s3 = Sequence {
    values = [2,3,5],
    steps = [2,4]
}
s3.preview(100) = [2,3,5,7,11,13,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,65,67,71,73,77,79,83,85,89,91,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,143,145,149,151,155,157,161,163,167,169,173,175,179,181,185,187,191,193,197,199,203,205,209,211,215,217,221,223,227,229,233,235,239,241,245,247,251,253,257,259,263,265,269,271,275,277,281,283,287,289,293,295,299,301,305]
```

## S4 - Non multiples of 2, 3 and 5, starting at 7
```javascript
val s3 = Sequence {
    values = [2,3,5,7],
    steps = [4,2,4,2,4,6,2,6]
}
s3.preview(100) = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,49,53,59,61,67,71,73,77,79,83,89,91,97,101,103,107,109,113,119,121,127,131,133,137,139,143,149,151,157,161,163,167,169,173,179,181,187,191,193,197,199,203,209,211,217,221,223,227,229,233,239,241,247,251,253,257,259,263,269,271,277,281,283,287,289,293,299,301,307,311,313,317,319,323,329,331,337,341,343,347,349,353,359,361,367,371,373,377,379]
```

## S5 - Non multiples of 2, 3, 5 and 7, starting at 11
```javascript
val s3 = Sequence {
    values = [2,3,5,7,11],
    steps = [2,4,2,4,6,2,6,4,2,4,6,6,2,6,4,2,6,4,6,8,4,2,4,2,4,8,6,4,6,2,4,6,2,6,6,4,2,4,6,2,6,4,2,4,2,10,2,10],
}
s3.preview(100) = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,121,127,131,137,139,143,149,151,157,163,167,169,173,179,181,187,191,193,197,199,209,211,221,223,227,229,233,239,241,247,251,253,257,263,269,271,277,281,283,289,293,299,307,311,313,317,319,323,331,337,341,347,349,353,359,361,367,373,377,379,383,389,391,397,401,403,407,409,419,421,431,433,437,439,443]
```

## S6 - Non multiples of 2, 3, 5, 7 and 11, starting at 13
```javascript
val s3 = Sequence {
    values = [2,3,5,7,11,13],
    steps = [4,2,4,6,2,6,4,2,4,6,6,2,6,4,2,6,4,6,8,4,2,4,2,4,14,4,6,2,10,2,6,6,4,2,4,6,2,10,2,4,2,12,10,2,4,2,4,6,2,6,4,6,6,6,2,6,4,2,6,4,6,8,4,2,4,6,8,6,10,2,4,6,2,6,6,4,2,4,6,2,6,4,2,6,10,2,10,2,4,2,4,6,8,4,2,4,12,2,6,4,2,6,4,6,12,2,4,2,4,8,6,4,6,2,4,6,2,6,10,2,4,6,2,6,4,2,4,2,10,2,10,2,4,6,6,2,6,6,4,6,6,2,6,4,2,6,4,6,8,4,2,6,4,8,6,4,6,2,4,6,8,6,4,2,10,2,6,4,2,4,2,10,2,10,2,4,2,4,8,6,4,2,4,6,6,2,6,4,8,4,6,8,4,2,4,2,4,8,6,4,6,6,6,2,6,6,4,2,4,6,2,6,4,2,4,2,10,2,10,2,6,4,6,2,6,4,2,4,6,6,8,4,2,6,10,8,4,2,4,2,4,8,10,6,2,4,8,6,6,4,2,4,6,2,6,4,6,2,10,2,10,2,4,2,4,6,2,6,4,2,4,6,6,2,6,6,6,4,6,8,4,2,4,2,4,8,6,4,8,4,6,2,6,6,4,2,4,6,8,4,2,4,2,10,2,10,2,4,2,4,6,2,10,2,4,6,8,6,4,2,6,4,6,8,4,6,2,4,8,6,4,6,2,4,6,2,6,6,4,6,6,2,6,6,4,2,10,2,10,2,4,2,4,6,2,6,4,2,10,6,2,6,4,2,6,4,6,8,4,2,4,2,12,6,4,6,2,4,6,2,12,4,2,4,8,6,4,2,4,2,10,2,10,6,2,4,6,2,6,4,2,4,6,6,2,6,4,2,10,6,8,6,4,2,4,8,6,4,6,2,4,6,2,6,6,6,4,6,2,6,4,2,4,2,10,12,2,4,2,10,2,6,4,2,4,6,6,2,10,2,6,4,14,4,2,4,2,4,8,6,4,6,2,4,6,2,6,6,4,2,4,6,2,6,4,2,4,12,2,12],
}
s3.preview(100) = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,169,173,179,181,191,193,197,199,211,221,223,227,229,233,239,241,247,251,257,263,269,271,277,281,283,289,293,299,307,311,313,317,323,331,337,347,349,353,359,361,367,373,377,379,383,389,391,397,401,403,409,419,421,431,433,437,439,443,449,457,461,463,467,479,481,487,491]
```

# Probabilistc Approach

If we just look up until the square of the maximum value of the Sequence, all the values returned should be prime.
But, differently of the Sieve of Eratosthenes, we can apply these sequences beyond their safe limits and they will still reduce the amount of elements that are not prime without removing any prime.

If we take the s6 above, for example, and try to evalute if the next 100 numbers from that sequence are prime, starting at 2310013, ``(s6.steps.sum() * 1000 + max(s6.values))``, we can see that 32% of them are primes.

```javascript
[2310019,2310029,2310043,2310067,2310083,2310107,2310137,2310157,2310167,2310193,2310211,2310221,2310223,2310233,2310241,2310277,2310289,2310293,2310311,2310331,2310349,2310359,2310367,2310389,2310421,2310431,2310439,2310449,2310463,2310479,2310481,2310491]
```
So, these Sequences can be used to evaluate all the prime numbers or can be used at some limit to reduce the number of non primes to be evaluated by some other algorithm.

# Benchmark

We are still working in the benchmark comparing the different implemementations.
