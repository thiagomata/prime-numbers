import * as mocha from 'mocha'
import { expect } from 'chai'

import { Cycle } from "../../../src/primes/sequences/cycle";

describe('SequenceList Tests', function () {

    let sequenceList: Cycle = null

    beforeEach(function () {
        sequenceList = new Cycle(1, 2, 3); // as SequenceList;
    })

    it('Test first', function () {
        const first = sequenceList.first();
        expect(first).to.eq(1)
    })

    it('Test last', function () {
        const last = sequenceList.last()
        expect(last).to.eq(3)
    })

    it('Circular Negative', function() {
        const circular = sequenceList.get(-1);
        expect(circular).to.eq(3)
    })

    it('Circular inbound', async function () {
        const circular = sequenceList.get(1);
        expect(circular).to.eq(2)
    })

    it('Circular outbound', function () {
        const circular = sequenceList.get(3);
        expect(circular).to.eq(1)
    })
});
