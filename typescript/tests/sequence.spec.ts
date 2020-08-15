import * as mocha from 'mocha'
import { expect } from 'chai'

import { Sequence } from "../src/sequence";
import { SequenceList } from '../src/sequenceList';

describe('Sequence Tests', function () {

    let sequence: Sequence = null

    beforeEach(function () {
        sequence = null;
    })

    it('Test first number from sequence', function () {
        sequence = Sequence.firstSequence;
        expect(sequence.currentNumber).to.eq(2);
    })

    it('Test first number from sequence', function () {
        sequence = Sequence.firstSequence;
        expect(sequence.steps).to.deep.equal([1] as SequenceList);
    })

    it('Test circular from steps from first sequence', function () {
        sequence = Sequence.firstSequence;
        expect(sequence.steps.circular(1)).to.deep.equal(1);
    })

    it('Test preview from sequence', function () {
        sequence = Sequence.firstSequence;
        expect(sequence.preview(10)).to.deep.equal([2,3,4,5,6,7,8,9,10,11]);
    })

    it('Test next, first 10 elements,no pair numbers', function () {
        sequence = Sequence.firstSequence.next();
        expect(sequence.preview(10)).to.deep.equal([2,3,5,7,9,11,13,15,17,19]);
    })


    it('Test next, no pair numbers until 10', function () {
        sequence = Sequence.firstSequence.next();
        expect(sequence.until(10)).to.deep.equal([2,3,5,7,9]);
    })

});