// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT license.

namespace Quantum.Kata.Superposition {

    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;


    //////////////////////////////////////////////////////////////////
    // Welcome!
    //////////////////////////////////////////////////////////////////

    // "Superposition" quantum kata is a series of exercises designed
    // to get you familiar with programming in Q#.
    // It covers the following topics:
    //  - basic single-qubit and multi-qubit gates,
    //  - superposition,
    //  - flow control and recursion in Q#.

    // Each task is wrapped in one operation preceded by the description of the task.
    // Each task (except tasks in which you have to write a test) has a unit test associated with it,
    // which initially fails. Your goal is to fill in the blank (marked with // ... comment)
    // with some Q# code to make the failing test pass.

    // The tasks are given in approximate order of increasing difficulty; harder ones are marked with asterisks.

    // Task 1. Plus state
    // Input: a qubit in the |0⟩ state.
    // Goal: prepare a |+⟩ state on this qubit (|+⟩ = (|0⟩ + |1⟩) / sqrt(2)).
    operation PlusState (q : Qubit) : Unit {
        // Hadamard gate H will convert |0⟩ state to |+⟩ state.
        // Type the following: H(q);
        // Then rebuild the project and rerun the tests - T01_PlusState_Test should now pass!

        H(q);
    }


    // Task 2. Minus state
    // Input: a qubit in the |0⟩ state.
    // Goal: prepare a |-⟩ state on this qubit (|-⟩ = (|0⟩ - |1⟩) / sqrt(2)).
    operation MinusState (q : Qubit) : Unit {
        // In this task, as well as in all subsequent ones, you have to come up with the solution yourself.
        H(q);
		Z(q);
    }


    // Task 3*. Unequal superposition
    // Inputs:
    //      1) a qubit in the |0⟩ state.
    //      2) angle alpha, in radians, represented as Double.
    // Goal: prepare a cos(alpha) * |0⟩ + sin(alpha) * |1⟩ state on this qubit.
    operation UnequalSuperposition (q : Qubit, alpha : Double) : Unit {
        // Hint: Experiment with rotation gates from the Microsoft.Quantum.Intrinsic namespace.
        // Note that all rotation operators rotate the state by _half_ of its angle argument.
		Ry(2.0 * alpha, q);
    }


    // Task 4. Superposition of all basis vectors on two qubits
    // Input: two qubits in |00⟩ state (stored in an array of length 2).
    // Goal:  create the following state on these qubits: (|00⟩ + |01⟩ + |10⟩ + |11⟩) / 2.
    operation AllBasisVectors_TwoQubits (qs : Qubit[]) : Unit {
        // The following lines enforce the constraints on the input that you are given.
        // You don't need to modify them. Feel free to remove them, this won't cause your code to fail.
        EqualityFactI(Length(qs), 2, "The array should have exactly 2 qubits.");
		H(qs[0]);
		H(qs[1]);
    }


    // Task 5. Superposition of basis vectors with phases
    // Input: two qubits in |00⟩ state (stored in an array of length 2).
    // Goal:  create the following state on these qubits: (|00⟩ + i*|01⟩ - |10⟩ - i*|11⟩) / 2.
    operation AllBasisVectorsWithPhases_TwoQubits (qs : Qubit[]) : Unit {
        // The following lines enforce the constraints on the input that you are given.
        // You don't need to modify them. Feel free to remove them, this won't cause your code to fail.
        EqualityFactI(Length(qs), 2, "The array should have exactly 2 qubits.");

		H(qs[0]);
		Z(qs[0]);

		H(qs[1]);
		S(qs[1]);
    }


    // Task 6. Bell state
    // Input: two qubits in |00⟩ state (stored in an array of length 2).
    // Goal: create a Bell state |Φ⁺⟩ = (|00⟩ + |11⟩) / sqrt(2) on these qubits.
    operation BellState (qs : Qubit[]) : Unit {
		H(qs[0]);
        CNOT(qs[0], qs[1]);
    }


    // Task 7. All Bell states
    // Inputs:
    //      1) two qubits in |00⟩ state (stored in an array of length 2)
    //      2) an integer index
    // Goal: create one of the Bell states based on the value of index:
    //       0: |Φ⁺⟩ = (|00⟩ + |11⟩) / sqrt(2)
    //       1: |Φ⁻⟩ = (|00⟩ - |11⟩) / sqrt(2)
    //       2: |Ψ⁺⟩ = (|01⟩ + |10⟩) / sqrt(2)
    //       3: |Ψ⁻⟩ = (|01⟩ - |10⟩) / sqrt(2)
    operation AllBellStates (qs : Qubit[], index : Int) : Unit {

		//Base bell state
		H(qs[0]);
		CNOT(qs[0], qs[1]);
		
		//Flip sign
		if (index == 1) {
			Z(qs[0]);
		}

		//Flip bit
		if (index == 2) {
			X(qs[0]);
		}

		//Flip sign and bit
		if (index == 3) {
			Z(qs[0]);
			X(qs[0]);
		}
    }


    // Task 8. Greenberger–Horne–Zeilinger state
    // Input: N qubits in |0...0⟩ state.
    // Goal: create a GHZ state (|0...0⟩ + |1...1⟩) / sqrt(2) on these qubits.
    operation GHZ_State (qs : Qubit[]) : Unit {
		H(qs[0]);
		for (i in 0..Length(qs)-2)
		{
			CNOT(qs[0], qs[i+1]);
		}
    }


    // Task 9. Superposition of all basis vectors
    // Input: N qubits in |0...0⟩ state.
    // Goal: create an equal superposition of all basis vectors from |0...0⟩ to |1...1⟩
    // (i.e. state (|0...0⟩ + ... + |1...1⟩) / sqrt(2^N) ).
    operation AllBasisVectorsSuperposition (qs : Qubit[]) : Unit {
		for (i in 0..Length(qs)-1)
		{
			H(qs[i]);
		}
    }


    // Task 10. Superposition of all even or all odd numbers
    // Inputs:
    //      1) N qubits in |0...0⟩ state.
    //      2) A boolean isEven.
    // Goal: create a superposition of all even numbers on N qubits if isEven is true,
    //       or a superposition of all odd numbers on N qubits if isEven is false.
    // 
    // A basis state encodes an integer number using big-endian binary notation: 
    // state |01⟩ corresponds to the integer 1, and state |10⟩ - to the integer 2. 
    //
    // Example: for N = 2 and isEven = true the required state is (|00⟩ + |10⟩) / sqrt(2), 
    //      and for N = 2 and isEven = false the required state is (|01⟩ + |11⟩) / sqrt(2).
    operation EvenOddNumbersSuperposition (qs : Qubit[], isEven : Bool) : Unit {
        
		mutable length = Length(qs);
		//Make all but the last one 50/50
		for (i in 0..length-2)
		{
			H(qs[i]);
		}

		//If even, keep the last one |0>, otherwise flip it to |1>
		if (not isEven)
		{
			X(qs[length-1]);
		}
    }


    // Task 11. |00⟩ + |01⟩ + |10⟩ state
    // Input: 2 qubits in |00⟩ state.
    // Goal: create the state (|00⟩ + |01⟩ + |10⟩) / sqrt(3) on these qubits.
    operation ThreeStates_TwoQubits (qs : Qubit[]) : Unit {
		//Rotate first qubit to have distributed probability
		// P(0) = 2/3, P(1) = 1/3
		let theta = ArcCos(Sqrt(2.0) / Sqrt(3.0));
		Ry(2.0 * theta, qs[0]);
        
		//If q[0] == |0>
		//	 q[1] = |+> (50/50 chance)
		// else
		//   q[1] = |0>
		(ControlledOnInt(0, H))([qs[0]], qs[1]);
    }


    // Task 12*. Hardy State
    // Input: 2 qubits in |00⟩ state
    // Goal: create the state (3|00⟩ + |01⟩ + |10⟩ + |11⟩) / sqrt(12) on these qubits.
    operation Hardy_State (qs : Qubit[]) : Unit {
		//Note that P(00) is not 3/6, but rather 9/12, as we square that portion and denominator to get the answer
		//P(00) = 0.75
		//P(01) = .083
		//P(10) = .083
		//P(11) = .083

		//P(0) = 0.75 + 0.083
		let theta0 = ArcCos(Sqrt(10.0 / 12.0));
		Ry(2.0 * theta0, qs[0]);

		//If |0>, 9/10 are 00, 1/10 are 01, so ArcCos(sqrt(9) / sqrt(10))
		let theta1 = 2.0 * ArcCos(3.0/Sqrt(10.0));
		(ControlledOnInt(0, Ry))([qs[0]], (theta1, qs[1]));

		//If |1>, 1/2 are 10, 1/2 are 11, so evenly distribute (PI / 4 from trig unit circle)
		let theta2 = 2.0 * (PI() / 4.0);
		(ControlledOnInt(1, H))([qs[0]], qs[1]);
    }


    // Task 13. Superposition of |0...0⟩ and given bit string
    // Inputs:
    //      1) N qubits in |0...0⟩ state
    //      2) bit string represented as Bool[]
    // Goal: create an equal superposition of |0...0⟩ and basis state given by the bit string.
    // Bit values false and true correspond to |0⟩ and |1⟩ states.
    // You are guaranteed that the qubit array and the bit string have the same length.
    // You are guaranteed that the first bit of the bit string is true.
    // Example: for bit string = [true, false] the qubit state required is (|00⟩ + |10⟩) / sqrt(2).
    operation ZeroAndBitstringSuperposition (qs : Qubit[], bits : Bool[]) : Unit {
        // The following lines enforce the constraints on the input that you are given.
        // You don't need to modify them. Feel free to remove them, this won't cause your code to fail.
        EqualityFactI(Length(bits), Length(qs), "Arrays should have the same length");
        EqualityFactB(bits[0], true, "First bit of the input bit string should be set to true");

		//First bit of the string is true, so we always want it to be 50/50
		H(qs[0]);

		for (i in 1..Length(qs)-1)
		{
			//skip bits that are false
			if (bits[i])
			{
				//If we care about a bit, make it 50/50
				CNOT(qs[0], qs[i]);
			}
		}
    }


    // Task 14. Superposition of two bit strings
    // Inputs:
    //      1) N qubits in |0...0⟩ state
    //      2) two bit string represented as Bool[]s
    // Goal: create an equal superposition of two basis states given by the bit strings.
    //
    // Bit values false and true correspond to |0⟩ and |1⟩ states.
    // Example: for bit strings [false, true, false] and [false, false, true]
    // the qubit state required is (|010⟩ + |001⟩) / sqrt(2).
    // You are guaranteed that the both bit strings have the same length as the qubit array,
    // and that the bit strings will differ in at least one bit.
    operation TwoBitstringSuperposition (qs : Qubit[], bits1 : Bool[], bits2 : Bool[]) : Unit {
		mutable firstDiff = -1;
		mutable firstDiffValue = false;

		//Find the first index that is different
		for (i in 0..Length(qs)-1)
		{
			if (bits1[i] != bits2[i] and firstDiff == -1)
			{
				set firstDiff = i;
				set firstDiffValue = bits1[i];
			}
		}

		//We know the firstDiff is 50/50, so set that
		H(qs[firstDiff]);

		for (i in 0..Length(qs)-1)
		{
			//If the values are the same, flip 1s to |1>
			if (bits1[i] == bits2[i])
			{
				if (bits1[i])
				{
					X(qs[i]);
				}
			}
			else
			{
				//Don't touch qs[firstDiff] as we are already happy with it
				if (i != firstDiff)
				{
					//If values are different, put them in a superposition
					CNOT(qs[firstDiff], qs[i]);

					//Keep the values in sync (0s with 0s, 1s with 1s)
					if (bits1[i] != firstDiffValue)
					{
						X(qs[i]);
					}
				}
			}
		}
    }


    // Task 15*. Superposition of four bit strings
    // Inputs:
    //      1) N qubits in |0...0⟩ state
    //      2) four bit string represented as Bool[][] bits
    //         bits is an array of size 4 x N which describes the bit strings as follows:
    //         bits[i] describes the i-th bit string and has N elements.
    //         All four bit strings will be distinct.
    //
    // Goal: create an equal superposition of the four basis states given by the bit strings.
    //
    // Example: for N = 3 and bits = [[false, true, false], [true, false, false], [false, false, true], [true, true, false]]
    //          the state you need to prepare is (|010⟩ + |100⟩ + |001⟩ + |110⟩) / 2.
    operation FourBitstringSuperposition (qs : Qubit[], bits : Bool[][]) : Unit {
        
		let N = Length(qs);

		using (anc = Qubit[2])
		{
			//Creates |00> + |01> | 10> + |11> state on anc
			H(anc[0]);
			H(anc[1]);

			//Tie anc = |00> to |010> on qs, |01> to |100>, etc. (for the example values)
			for (i in 0..3)
			{
				for (j in 0..N-1)
				{
					if (bits[i][j])
					{
						(ControlledOnInt(i, X))(anc,qs[j]);
					}
				}
			}

			//Reset anc back to |00>, by removing |01>, |10> and |11>
			//Note that we don't need to control on |00>, since it's already what we want
            (ControlledOnBitString(bits[1], X))(qs, anc[0]);

			(ControlledOnBitString(bits[2], X))(qs, anc[1]);

			(ControlledOnBitString(bits[3], X))(qs, anc[0]);
			(ControlledOnBitString(bits[3], X))(qs, anc[1]);
		}
        // ...
    }


    // Task 16**. W state on 2ᵏ qubits
    // Input: N = 2ᵏ qubits in |0...0⟩ state.
    // Goal: create a W state (https://en.wikipedia.org/wiki/W_state) on these qubits.
    // W state is an equal superposition of all basis states on N qubits of Hamming weight 1.
    // Example: for N = 4, W state is (|1000⟩ + |0100⟩ + |0010⟩ + |0001⟩) / 2.
    operation WState_PowerOfTwo (qs : Qubit[]) : Unit {
        // Hint: you can use Controlled modifier to perform arbitrary controlled gates.
		
		let N = Length(qs);
		
		if (N == 1)
		{
			//Default case: |1> is the W state on N = 1
			X(qs[0]);
		}
		else
		{
			let K = N / 2;
			WState_PowerOfTwo(qs[0..K-1]);

			using (anc = Qubit())
			{
				H(anc);

				for (i in 0..K-1)
				{
					//For N = 8
					//K = 4
					//SWAP(0, 4), SWAP(1,5), SWAP(2,6), SWAP(3,7)
					Controlled SWAP([anc], (qs[i], qs[i+K]));
				}
				for (i in K..N-1)
				{
					//Reset anc to |0>
					CNOT(qs[i], anc);
				}
			}
		}
    }


    // Task 17**. W state on arbitrary number of qubits
	// Recursive approach
    // Input: N qubits in |0...0⟩ state (N is not necessarily a power of 2).
    // Goal: create a W state (https://en.wikipedia.org/wiki/W_state) on these qubits.
    // W state is an equal superposition of all basis states on N qubits of Hamming weight 1.
    // Example: for N = 3, W state is (|100⟩ + |010⟩ + |001⟩) / sqrt(3).
    operation WState_Arbitrary_Recursive (qs : Qubit[]) : Unit is Adj + Ctl {
        let N = Length(qs);

		if (N == 1)
		{
			//Set the value of qs[0] to |1>
			X(qs[0]);
		}
		else
		{
			//For N = 4, we want [0: 1/4, 1: 3/4 * 1/3, 2: 3/4 * (2/3 * 1/2) , 3: 3/4 * (2/3 * 1/2)]
			//We do 1/4 qs[0], 3/4 the rest, then 1/3 qs[1], 2/3 the rest, etc.

			//for N = 4, angle = 1/sqrt(4)
			let angle = ArcSin(1.0 / Sqrt(IntAsDouble(N)));
			Ry(2.0 * angle, qs[0]);

			//Flip qs[0] to be the opposite, so from 1/4 to 3/4, or 1/8 to 7/8
			X(qs[0]);

			//If qs[0] == |1>, the rest are 0.
			//Else, run the algorithm on the rest of the set, so if qs[0] == |0> and qs[1] == |1>, the rest are 0, etc.
			Controlled WState_Arbitrary_Recursive(qs[0..0], qs[1..N-1]);

			//Flip qs back to its original weight
			X(qs[0]);
		}
    }

	// Task 17**. W state on arbitrary number of qubits
	// Iterative approach
    // Input: N qubits in |0...0⟩ state (N is not necessarily a power of 2).
    // Goal: create a W state (https://en.wikipedia.org/wiki/W_state) on these qubits.
    // W state is an equal superposition of all basis states on N qubits of Hamming weight 1.
    // Example: for N = 3, W state is (|100⟩ + |010⟩ + |001⟩) / sqrt(3).
    operation WState_Arbitrary_Iterative (qs : Qubit[]) : Unit is Adj {
        let N = Length(qs);

	}

	// Task 17**. W state on arbitrary number of qubits
	// Power of Two approach
    // Input: N qubits in |0...0⟩ state (N is not necessarily a power of 2).
    // Goal: create a W state (https://en.wikipedia.org/wiki/W_state) on these qubits.
    // W state is an equal superposition of all basis states on N qubits of Hamming weight 1.
    // Example: for N = 3, W state is (|100⟩ + |010⟩ + |001⟩) / sqrt(3).
	operation WState_Arbitrary_Postselect (qs : Qubit[]) : Unit {

	}
}
