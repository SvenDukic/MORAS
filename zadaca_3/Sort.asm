(LOOP_START)
	@0
	D = M

	@LOOP_END
	D;JEQ

	@100
	D = D - 1
	D = A + D
	A = D
	D = M

	@i
	M = D

	@0
	D = M

	@1
	M = D - 1

	@i
	D = M

	@x
	M = D

	@0
	D = M

	@maksimum
	M = D
	
	(SECOND_LOOP)
		@1
		D = M
	
		@SECOND_LOOP_END
		D;JEQ
	
		@100
		D = D-1
		D = A + D
		A = D
		D = M
	
		@n
		M = D
	
		@x
		D = M - D
	
		@ABCD
		D;JGT
	
		@n
		D = M
	
		@x
		M = D
	
		@1
		D = M
	
		@maksimum
		M = D
	
		(ABCD)
		@1
		M = M - 1
	
		@SECOND_LOOP
		0;JMP
	(SECOND_LOOP_END)
	
	@0
	D = M

	@100
	D = A

	@0
	D = D + M

	@temp
	M = D - 1

	@x
	D = M

	@temp
	A = M
	M = D

	@100
	D = A

	@maksimum
	D = D + M

	@temp
	M = D - 1

	@i
	D = M

	@temp
	A = M
	M = D

	@0
	M = M - 1

	@LOOP_START
	0;JMP
(LOOP_END)

(END)
@END
0;JMP
