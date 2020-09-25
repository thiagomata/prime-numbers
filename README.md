# Sequences in Prime Numbers
A small study about prime numbers using different approaches and programming languages.

## Sequences and Steps

This study intends to compare different ways to calculate prime numbers, especially related to evaluating one (possible new?) way using sequences and steps.

## Avoiding pair numbers

One widespread improvement to the classic prime search is avoiding evaluate pair numbers different of the number 2. This is because after 2, all pair numbers are not prime, and we should avoid wasting time considering them.

So, if we look at the numbers evaluated by this solution, we would see something like:

```java
[2,3,5,7,9,11,13,15,17,...]
```

One different way to see this is looking at the distance between the numbers after separating the previously found primes. In this study, we are naming this distance between the numbers that we should evaluate as "steps". Also, we are calling the previous values as "values" and the struct with the "values" and "steps" as "Sequence".

```java
// Example of Sequence that loads 2, 3 and them all the non pair values
val s2 = Sequence {
    values: [2,3]
    steps: [2,2,2,2,2....]
}
```

Basically, after loading all the previous found values, we keep our list applying the steps. As you can see, the steps in this particular list are always the same. So, considering that this is a cycle list, that is, after loading the last element we are going to return to the first, we can rewrite our Sequence in this format:

```java
// Same Sequence, but more compact
val s2 = Sequence {
    values: [2,3]
    steps: [2]
}
```

## Creating a new sequence based on the previous

The question that started this study is if it would be possible to create more complex Sequences that would avoid multiples of other prime numbers. More importantly, if it is possible to create a sequence that avoids the next prime number based on the current Sequence.

Let's consider the Sequence that should avoid the multiples of 2 and 3. That Sequence should be like this:

```java
s3 = Sequence {
    values: [2,3,5]
    steps: [2,4]
}
```

In other words, after loading the values `[2, 3, 5]`, the Sequence should keep following adding the values `[2,4]`, in a loop, to avoid the multiples of 2 and 3. We can see that the result of that operation should be:

```java
[2,3,5,7,11,13,17,19,23,...]
```

So, how can we create this new Sequence based on the previous one? How can we create the next sequence method to work as described as follows?

```java
// in this particular case
val Sequence s3 = s2.nextSequence()
// in the general case
val Sequence nextSequence = currentSequence.nextSequence()
```

First, we had to find the next value. Then, we have to create new steps.

### Current Last value

The goal is to create a new list that avoids multiples of 2 and 3. Generally speaking, we want to create a new Sequence that keeps avoiding the previous multiples and also avoids the multiples of the current last value.
So, we are going to call the number 3 as our current last value.

```java
Sequence.getCurrentLastValue(): Integer {
   return max(currentSequence.values)
}

val s2.getCurrentLastValue = max([2,3]) = 3
```

### Next value
Loading the next step is a trivial operation. Since we are avoiding all the numbers that are multiples from the previous values, the following number in the Sequence should be our next value.

```java
Sequence.getNextValue(): Integer {
  return this.getCurrentLastValue() + this.step[0] 
}
val s2.getNextValue() = 3 + 2 = 5
```

### Next steps

To define the next step, we must first multiply our list by the next value. That is, in this particular case, that we are repeating three times the previous one.

```java
currentSequence.steps.repeat(currentLastValue) = [2,2,2]
```

We can see that the sum of the values of this new list of steps (6 in this case) will be multiple by both values 2 and 3. That is important because that ensures that when we cycle the list, the mod result will be the same.
Then, we create an accumulator that starts with the next value (5) and walks through our new list. If some element is multiple of the current value, the result should be the present value plus the next one.

```java
Sequence.getNextSteps(): Array<Integer> {
   val currentLastValue = this.getCurrentLastValue();
   val stepsToEvaluate = this.steps.repeat(currentLastValue);
   var accumulator = this.getNextValue();
   var newSteps: Array<Integer> = [];
   stepsToEvaluate.foreach(
      (currentElement) => {
          val currentElement = stepsToEvaluate[ i ];
          if ( ( accumulator + currentElement ) mod currentLastValue == 0 ) {
            val previousElement = newSteps.pop();
            newSteps.push( previousElement + currentElement );
          } else {
             newSteps.push( currentElement );
          }
          accumulator += currentElement;
      }
   )
   return newSteps;
}

s2.getNextSteps() = [2,4]
```

We can say that the new list will create a list avoiding the multiples from the old and new Sequences because:
The sum of the new steps is multiple the current element;
We are avoiding all the steps that would collide with a multiple of the next elements;
We are still avoiding the same elements from the previous list;
Since the sum of the steps is multiple from the current element, when we rerun the steps in a cycle, the mod should also be in the same cycle.

So, it is possible to create a new Sequence based on the previous one.

## Implemementation

You can find an implementation of this algorithm in this project using Javascript, TypesScript and Haskell in this project. Also, we are working in ways to compare the performance of this solution with the traditional ones.
Each implementation has its particularities.  We will add more comments to each one of them as soon as possible.

## Sequences

### S1 - All natural numbers, starting at 2
Using the presented definiton, we can define the first sequence as

```java
val s1 = Sequence {
    values: [2],
    steps: [1]
}
s1.preview(100) = [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102]
```

That should include all integer numbers bigger than 1.

### S2 - Non-multiples of 2, starting at 3
```java
val s2 = Sequence {
    values = [3,2], 
    steps = [2]
}
s2.preview(100) = [2,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35,37,39,41,43,45,47,49,51,53,55,57,59,61,63,65,67,69,71,73,75,77,79,81,83,85,87,89,91,93,95,97,99,101,103,105,107,109,111,113,115,117,119,121,123,125,127,129,131,133,135,137,139,141,143,145,147,149,151,153,155,157,159,161,163,165,167,169,171,173,175,177,179,181,183,185,187,189,191,193,195,197,199,201,203]
```

### S3 - Non-multiples of 2 and 3,starting at 5
```java
val s3 = Sequence {
    values = [2,3,5],
    steps = [2,4]
}
s3.preview(100) = [2,3,5,7,11,13,17,19,23,25,29,31,35,37,41,43,47,49,53,55,59,61,65,67,71,73,77,79,83,85,89,91,95,97,101,103,107,109,113,115,119,121,125,127,131,133,137,139,143,145,149,151,155,157,161,163,167,169,173,175,179,181,185,187,191,193,197,199,203,205,209,211,215,217,221,223,227,229,233,235,239,241,245,247,251,253,257,259,263,265,269,271,275,277,281,283,287,289,293,295,299,301,305]
```

### S4 - Non-multiples of 2, 3 and 5, starting at 7
```java
val s4 = Sequence {
    values = [2,3,5,7],
    steps = [4,2,4,2,4,6,2,6]
}
s4.preview(100) = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,49,53,59,61,67,71,73,77,79,83,89,91,97,101,103,107,109,113,119,121,127,131,133,137,139,143,149,151,157,161,163,167,169,173,179,181,187,191,193,197,199,203,209,211,217,221,223,227,229,233,239,241,247,251,253,257,259,263,269,271,277,281,283,287,289,293,299,301,307,311,313,317,319,323,329,331,337,341,343,347,349,353,359,361,367,371,373,377,379]
```

### S5 - Non-multiples of 2, 3, 5 and 7, starting at 11
```java
val s5 = Sequence {
    values = [2,3,5,7,11],
    steps = [2,4,2,4,6,2,6,4,2,4,6,6,2,6,4,2,6,4,6,8,4,2,4,2,4,8,6,4,6,2,4,6,2,6,6,4,2,4,6,2,6,4,2,4,2,10,2,10],
}
s5.preview(100) = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,121,127,131,137,139,143,149,151,157,163,167,169,173,179,181,187,191,193,197,199,209,211,221,223,227,229,233,239,241,247,251,253,257,263,269,271,277,281,283,289,293,299,307,311,313,317,319,323,331,337,341,347,349,353,359,361,367,373,377,379,383,389,391,397,401,403,407,409,419,421,431,433,437,439,443]
```

### S6 - Non-multiples of 2, 3, 5, 7 and 11, starting at 13
```java
val s6 = Sequence {
    values = [2,3,5,7,11,13],
    steps = [4,2,4,6,2,6,4,2,4,6,6,2,6,4,2,6,4,6,8,4,2,4,2,4,14,4,6,2,10,2,6,6,4,2,4,6,2,10,2,4,2,12,10,2,4,2,4,6,2,6,4,6,6,6,2,6,4,2,6,4,6,8,4,2,4,6,8,6,10,2,4,6,2,6,6,4,2,4,6,2,6,4,2,6,10,2,10,2,4,2,4,6,8,4,2,4,12,2,6,4,2,6,4,6,12,2,4,2,4,8,6,4,6,2,4,6,2,6,10,2,4,6,2,6,4,2,4,2,10,2,10,2,4,6,6,2,6,6,4,6,6,2,6,4,2,6,4,6,8,4,2,6,4,8,6,4,6,2,4,6,8,6,4,2,10,2,6,4,2,4,2,10,2,10,2,4,2,4,8,6,4,2,4,6,6,2,6,4,8,4,6,8,4,2,4,2,4,8,6,4,6,6,6,2,6,6,4,2,4,6,2,6,4,2,4,2,10,2,10,2,6,4,6,2,6,4,2,4,6,6,8,4,2,6,10,8,4,2,4,2,4,8,10,6,2,4,8,6,6,4,2,4,6,2,6,4,6,2,10,2,10,2,4,2,4,6,2,6,4,2,4,6,6,2,6,6,6,4,6,8,4,2,4,2,4,8,6,4,8,4,6,2,6,6,4,2,4,6,8,4,2,4,2,10,2,10,2,4,2,4,6,2,10,2,4,6,8,6,4,2,6,4,6,8,4,6,2,4,8,6,4,6,2,4,6,2,6,6,4,6,6,2,6,6,4,2,10,2,10,2,4,2,4,6,2,6,4,2,10,6,2,6,4,2,6,4,6,8,4,2,4,2,12,6,4,6,2,4,6,2,12,4,2,4,8,6,4,2,4,2,10,2,10,6,2,4,6,2,6,4,2,4,6,6,2,6,4,2,10,6,8,6,4,2,4,8,6,4,6,2,4,6,2,6,6,6,4,6,2,6,4,2,4,2,10,12,2,4,2,10,2,6,4,2,4,6,6,2,10,2,6,4,14,4,2,4,2,4,8,6,4,6,2,4,6,2,6,6,4,2,4,6,2,6,4,2,4,12,2,12],
}
s6.preview(100) = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,169,173,179,181,191,193,197,199,211,221,223,227,229,233,239,241,247,251,257,263,269,271,277,281,283,289,293,299,307,311,313,317,323,331,337,347,349,353,359,361,367,373,377,379,383,389,391,397,401,403,409,419,421,431,433,437,439,443,449,457,461,463,467,479,481,487,491]
```
# Probabilistic Approach

If we look up until the square of the maximum value of the Sequence, all the values returned should be prime. But, differently from the Sieve of Eratosthenes, we can apply these sequences beyond their safe limits, and they will still reduce the number of elements that are not prime without removing any prime.
If we take the s6 above, for example, and try to evaluate if the next 100 numbers from that Sequence are prime, starting at 2310013, (s6.steps.sum() * 1000 + max(s6.values)), we can see that 32% of them are primes.

```java
[2310019,2310029,2310043,2310067,2310083,2310107,2310137,2310157,2310167,2310193,2310211,2310221,2310223,2310233,2310241,2310277,2310289,2310293,2310311,2310331,2310349,2310359,2310367,2310389,2310421,2310431,2310439,2310449,2310463,2310479,2310481,2310491]
```
So, Sequences can evaluate all the prime numbers and can reduce the number of non-primes evaluated by some other algorithm.
Benchmark
We are still working in the benchmark comparing the different implementations.
