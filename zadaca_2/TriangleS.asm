//16384 + (512*4) + 8

@22511
D = A
@adfordia
M = D
@15
D = A
@cnt
M = D 
@k 
M = 0

(Diagonal_Line_Start)
  @k 
  D = M
  @127
  D = D - A
  @Diagonal_Line_End
  D; JGE
  
  //dijagonalu crtamo tako da postavljamo bitove na 0..1, 0..10, 0..100 (M = M + D), itd, a cnt sluzi da svakih 16 bitova (kad prodemo sve bitove),
  //postavimo da opet od pocetka ide
  @g
  M = 0
  @adfordia
  A = M
  M = 1
  (LOOP_START)
    @g
	D = M
    @cnt
    D = M - D 
    @LOOP_END
    D; JEQ
  
    @adfordia
    A = M
	D = M
    M = M + D  //"setam" tocku dok ne dode na svoje mjesto u dijagonali
  
    @g
    M = M + 1
  
    @LOOP_START
    0; JMP 
  (LOOP_END)
  
  
  @cnt 
  D = M
  @0
  D = D - A
  @SkokRegistra
  D; JEQ
  (Povratak)
  
  @32
  D = A
  @adfordia 
  M = M - D //skok za 32 mjesta prema gore (tj za jedan registar gore)
  @k  
  M = M + 1
  @cnt
  M = M - 1
  
  @Diagonal_Line_Start
  0; JMP
(Diagonal_Line_End)

@Nastavak
0; JMP

(SkokRegistra)
@adfordia
M = M - 1  //kad cnt dode na 0, pomicemo se jedan registar ulijevo
@15
D = A
@cnt 
M = D + 1
@Povratak 
0; JMP

(Nastavak)
@18440
D = A

@address
M = D

@i 
M = 0

(Vertical_Line_Start)
  //petlja
  @i
  D = M
  @127
  D = D - A
  @Vertical_Line_End
  D; JGE
  
   
  @address
  A = M  //spremimo u adresni registar, adresiramo memoriju na koju pokazuje A i postavimo na M+1
  M = M + 1 //gornji dio dijagonale je upisan u isti registar kao i gornji dio vertikale (tj prvi registar) 
	
  @i 
  M = M + 1
	
  //povecaj adresu za 32
  @32
  D = A
	
  @address 
  M = M + D  //prebacujemo se u registar prema dolje pa ide +32
  
  //bezuvjetni skok
  @Vertical_Line_Start
  0; JMP
(Vertical_Line_End)


@j
M = 0

(Horizontal_Line_Start)
  @j
  D = M
  @8
  D = D - A
  @Horizontal_Line_End
  D; JGE 
  
  //svaki registar sadrzi 16 piksela, mi zelimo 8 registara (8*16=128) obojati u crno
  // ak zelimo svaki piksel u registru obojati u crno, stavimo M = -1
  @address
  A = M
  M = -1
  
  @j
  M = M + 1
  
  @address
  M = M + 1 //prebacujemo se jedan registar udesno pa ide +1
  
  @Horizontal_Line_Start
  0; JMP
(Horizontal_Line_End)

(End)
@End
0; JMP

 
  