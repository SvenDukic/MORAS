//ako je baza = 1, vrati = 1
@0
D = M
@POT_JEDAN
D-1;JEQ

@1
D = M

@e
M = D

@RACUNANJE
D;JGT


//ako je eksponent = 0, vrati 1
@2
M = 1
@END
0;JMP

(POT_JEDAN)
@2
M = 1
@END
0;JMP

(RACUNANJE)
@0
D = M

@i
M = D

@2
M = D

@j
M = D


(LOOP_START)
	@e
	D = M

	@LOOP_END
	D-1;JEQ
	(SECOND_LOOP_START)
		@i
		D = M
		@SECOND_LOOP_END
		D-1;JEQ
		
		@j
		D = M
		@2
		M = M + D
		@i
		M = M - 1
	@SECOND_LOOP_START
	0;JMP
	(SECOND_LOOP_END)
	
	@2
	D = M
	@j
	M = D
	@0
	D = M
	@i
	M = D
	@e
	M = M - 1
	@LOOP_START
	0;JMP
(LOOP_END)

(END)
@END
0;JMP