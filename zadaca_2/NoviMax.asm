// Za pocetak stavimo u RAM[5] vrijednost koja se nalazi u RAM na indeksu 0 i to je trenutna maksimalna vrijednost
// Iteriramo od 0 do 4
// Address oznacava i+1 adresu (jer smo RAM na indeksu 0 upisali kao maksimum pa krecemo od vrijednosti RAM[i+1]=RAM[0+1]=RAM[1]),
// kojoj cemo uzeti vrijednost,a onda usporedivati s maksimumom (vrijednosti RAM[5])
// Ako je razlika izmedu vrijednosti RAM-a u iteraciji i RAM[5] veca od 0, to znaci da moramo upisati novu najvecu vrijednost (skacemo na NoviMax)
// Odradimo zamjenu i vratimo se nazad (skocimo na Povratak)
// Povecamo varijablu i po kojoj iteriramo i address za 1 i nastavljamo na isti nacin
// Sve zavrsavamo bezuvjetnom petljom:
// (End)
// @End 
// 0; JMP



@i
M = 0

@i
D = M

@address
M = D + 1

@R0
D = M
@R5
M = D

(LOOP_START)
  @i
  D = M
  @4
  D = D - A
  @LOOP_END
  D; JGE
  
  @address
  D = M
  A = D 
  D = M
  
  @R5
  D = D - M
  @NoviMax
  D; JGT
  (Povratak)
  
  @i 
  M = M + 1
  @address
  M = M + 1
  @LOOP_START
  0; JMP
(LOOP_END)
(END)
@END
0;JMP

(NoviMax)
@address
D = M
A = D
D = M
@R5
M = D
@Povratak
0; JMP