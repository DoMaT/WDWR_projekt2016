/*********************************************
 * OPL 12.5.1.0 Model
 * Author: Mateusz
 * Creation Date: May 25, 2016 at 7:55:31 PM
 *********************************************/
 
  //***************Sta³e opisuj¹ce problem************************
 int liczbaZmiennych = ...;
 int liczbaScenariuszy = ...;
 int liczbaKomponentow = ...;
 int liczbaMiesiecy = ...;
 
 range zakresZmiennych = 1 .. liczbaZmiennych;
 range zakresScenariuszy = 1 .. liczbaScenariuszy;
 range zakresKomponentow = 1 .. liczbaKomponentow;
 range zakresMiesiecy = 1 .. liczbaMiesiecy;
  
 
 
 int umowa[zakresKomponentow] = ...;
 
 int mozliweDostawyZ1[zakresMiesiecy] = ...;
 int mozliweDostawyZ2[zakresMiesiecy] = ...;
 
 float zapotrzebowanieZ1[zakresKomponentow] = ...;
 float zapotrzebowanieZ2[zakresKomponentow] = ...;
 
 float kosztProdukcji[zakresScenariuszy][zakresZmiennych] = ...;
  
  //*********************Zmienne decyzyjne ****************
  //liczba sztuk wyprodukowanego elementu A/B w danym miesi¹cu M1/M2/M3
 dvar int+ produkcjaKomp[zakresKomponentow][zakresMiesiecy];

  //stan magazynu
 dvar int+ magazyn[zakresMiesiecy];
 
  //zmienna binarna oznaczaj¹ca przekroczenie produkcji w wysokoœci 100 sztuk
  //miesiecznie dla wszystkich komponentow
 dvar boolean prodPowyzej100[zakresMiesiecy];
 //miesiecznie dla jednego komponentu
 dvar boolean prodPowyzej100Komp[zakresKomponentow][zakresMiesiecy];
 
  //iloœæ u¿ytego zasobu produkcyjnego Z1/Z2 na wytworzenie komponentu A/B w danym miesi¹cu
 dvar float uzycieZ1[zakresKomponentow][zakresMiesiecy];
 dvar float uzycieZ2[zakresKomponentow][zakresMiesiecy];
 
 
  //********************Zmienne stanu (wyra¿enia decyzji)*****************************
  //Kryteria
  //Koszt produkcji = produkcja komponentów * koszt produkcji komponentów
 dexpr float koszt[s in zakresScenariuszy] = 
 	sum (k in zakresKomponentow, m in zakresMiesiecy)
   	(
   		(kosztProdukcji[s][3*(k-1)+m] * produkcjaKomp[k][m]) * 1.1  //*1 - ca³kowity koszt produkcji
   		+ (kosztProdukcji[s][3*(k-1)+m] * (produkcjaKomp[k][m] - 100)) * (0.05 * prodPowyzej100[m] /** prodPowyzej100Komp[k][m]*/) //powoduje b³¹d nieliniowoœci. bez tej flagi odejmuje 100 od kazdej wartosci dla ktorej liczony jest dodatkowy koszt skladowania
   	);
   	
 dexpr float calkowityKosztProdukcji[s in zakresScenariuszy] = 
 	sum (k in zakresKomponentow, m in zakresMiesiecy)
   	(
   		(kosztProdukcji[s][3*(k-1)+m] * produkcjaKomp[k][m])
   	);
   	
 dexpr float sredniKoszt = 
 	(sum(s in zakresScenariuszy)
 		(
 			calkowityKosztProdukcji[s]
 		)
 	) / liczbaScenariuszy;
 
 dexpr float ryzyko = (1 / (2 * liczbaScenariuszy * liczbaScenariuszy))
 	* sum (s1 in zakresScenariuszy, s2 in zakresScenariuszy)
 	(
 		abs(calkowityKosztProdukcji[s1] - calkowityKosztProdukcji[s2])
 	);
 
 
// minimize sredniKoszt + ryzyko * 0; //utopia kosztu i nadir ryzyka
 minimize ryzyko + sredniKoszt * 0; //utopia ryzyka i nadir kosztu
 
 
 //Ograniczenia
 subject to
 {
   Umowa:
     forall(k in zakresKomponentow)
        sum(m in zakresMiesiecy) produkcjaKomp[k][m] == umowa[k];
        
   UzycieZ1:
     forall(k in zakresKomponentow)
       forall(m in zakresMiesiecy)
     		uzycieZ1[k][m] == produkcjaKomp[k][m] * zapotrzebowanieZ1[k];
   
   UzycieZ2:
     forall(k in zakresKomponentow)
       forall(m in zakresMiesiecy)
     		uzycieZ2[k][m] == produkcjaKomp[k][m] * zapotrzebowanieZ2[k];
   
   StanMagazynu:
     forall(m in zakresMiesiecy)
   		magazyn[m] == sum(k in zakresKomponentow) produkcjaKomp[k][m];
   		
   PrzekroczenieKosztowSuma:
     forall(m in zakresMiesiecy)
      {
       		magazyn[m] <= 100 + 1200 * prodPowyzej100[m];
       		magazyn[m] >= 100 * prodPowyzej100[m];
      }       	
   
   PrzekroczenieKosztow:
     forall(m in zakresMiesiecy)
       forall(k in zakresKomponentow)
         {
           	produkcjaKomp[k][m] <= 100 + 1200 * prodPowyzej100Komp[k][m];
           	produkcjaKomp[k][m] >= 100 * prodPowyzej100Komp[k][m];
         }           
   
   MaksDostawa:
     forall(m in zakresMiesiecy)
       {
         	sum(k in zakresKomponentow) uzycieZ1[k][m] <= mozliweDostawyZ1[m];
			sum(k in zakresKomponentow) uzycieZ2[k][m] <= mozliweDostawyZ2[m];
       }         

   MinimalnaProdukcja:
     forall(m in zakresMiesiecy)
       forall(k in zakresKomponentow)
         produkcjaKomp[k][m] >= 0;
   
 }   
 