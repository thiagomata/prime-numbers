import { SequenceList } from "./sequenceList";

export class Sequence {
  constructor(
    readonly steps: SequenceList,
    readonly previousSteps: SequenceList,
    readonly currentNumber: number,
    readonly previousNumbers: SequenceList
  ) {}

  public getNextNumber(): number {
    return this.currentNumber + this.steps.first();
  }

  public static reduceStep(
    buildingStep: Array<number>,
    currentNumber: number,
    nextNumber: number
  ): SequenceList {
    let acc: number = nextNumber;
    let pass: number = 0;
    let result: SequenceList = new SequenceList();
    buildingStep.forEach((value) => {
      acc += value;
      if (acc % currentNumber === 0) {
        pass += value;
      } else {
        value += pass;
        pass = 0;
        result.push(value);
      }
    });
    if (pass !== 0) {
      // we could not find a solution that avoid the multiples of the currentNumber
      // combining the current steps
      throw new Error(
        "unable to find a possible answer to the reduce step " + pass
      );
    }
    return result;
  }

  public next(): Sequence {
    let previousSteps = this.steps;
    let buildingSteps = this.steps.rotateRight();
    let nextNumber = this.getNextNumber();
    let addStep = [].concat(buildingSteps);
    let loopStep = new SequenceList();
    do {
      loopStep = loopStep.concat(addStep);
      let totalStep = loopStep.sum();
      if (totalStep % this.currentNumber != 0) {
        continue;
      }
      loopStep = Sequence.reduceStep(loopStep, this.currentNumber, nextNumber);
    } while (loopStep.sum() % this.currentNumber !== 0);

    return new Sequence(
      loopStep,
      previousSteps,
      nextNumber,
      this.previousNumbers.concat(nextNumber)
    );
  }

  public preview(size: number = 100): Array<number> {
    let preview = [].concat(this.previousNumbers);
    let circularValue = 0;
    for (let i = preview.length; i < size; i++) {
      preview[i] = preview[i - 1] + this.steps.circular(circularValue);
      circularValue++;
    }
    return preview;
  }

  public static readonly firstSequence = new Sequence(
    new SequenceList().concat(1),
    new SequenceList().concat(0),
    2,
    new SequenceList().concat(2)
  );

  public until(last = 100): Array<number> {
    let preview = new SequenceList().concat(this.previousNumbers);
    if( preview.last() >= last ) {
      return preview.filter( v => v <= last );
    }
    
    let circularCounter = 0;
    let i = preview.length
    while (preview.last() < last ) {
      preview[i] = preview[i - 1] + this.steps.circular(circularCounter);
      circularCounter++;
      i++
    }
    return preview.filter( p => p <= last );
  };

  public static allPrimesUntil(n: number): Array<number> {
    let sequence =  Sequence.firstSequence;
    let sqrtN = Math.sqrt(n);
    while(sequence.currentNumber <= sqrtN ) {
        sequence = sequence.next();
    }
    return sequence.until(n);
  }
}
