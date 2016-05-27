/*********************************************
 * OPL 12.5.1.0 Model
 * Author: Mateusz
 * Creation Date: 05-05-2016 at 22:52:11
 *********************************************/

 //***************Sta³e opisuj¹ce problem************************
 //Limity dostawy zasobów produkcyjnych [posSup - possible supply] Z1/Z2 w danym miesi¹cu M1/M2/M3
 float posSupZ1M1 = ...;
 float posSupZ1M2 = ...;
 float posSupZ1M3 = ...;
 float posSupZ2M1 = ...;
 float posSupZ2M2 = ...;
 float posSupZ2M3 = ...;
 
 //Realizacja umowy wymaga dostawy [need] okreœlonej liczby sztuk komponentu A/B
 float needA = ...;
 float needB = ...;

 //Zapotrzebowanie na sztukê zasobu produkcyjnego przy produkcji komponentów A i B [part of Z1/Z2 in A/B]
 float partOfZ1inA = ...;
 float partOfZ1inB = ...;
 float partOfZ2inA = ...;
 float partOfZ2inB = ...;
 
 //Wektor wartoœci oczekiwanych
 int expectedValueSize = ...;
 range rangeExpectedValue = 1 .. expectedValueSize;
 float expectedValue[rangeExpectedValue] = ...;
 
 //Scenariusze kosztu produkcji
 int scenarioSize = ...;
 range rangeScenario = 1 .. scenarioSize;
 float scenario[rangeScenario][rangeExpectedValue] = ...;
 
 //Metoda punktu odniesienia
 float costAspiration = ...;
 float riskAspiration = ...;
 
 float costLambda = ...;
 float riskLambda = ...;
 float epsilon = ...;
 float beta = ...;

//*********************Zmienne decyzyjne ****************
//liczba sztuk wyprodukowanego elementu A/B w danym miesi¹cu M1/M2/M3
dvar float AM1; 
dvar float AM2;
dvar float AM3;
dvar float BM1;
dvar float BM2;
dvar float BM3; 

//flagi oznaczaj¹ce przekroczenie produkcji 100 sztuk komponentu miesiêcznie
dvar boolean month1Over100; //true if AM1+AM2>100
dvar boolean month2Over100;
dvar boolean month3Over100;
dvar boolean month1Below100; //true if AM1+AM2 <=100
dvar boolean month2Below100;
dvar boolean month3Below100;


//********************Zmienne stanu (wyra¿enia decyzji)*****************************
//liczba kupowanych zasobów Z1/Z2 w miesi¹cu M1/M2/M3
dexpr float Z1M1 = AM1 * partOfZ1inA + BM1 * partOfZ1inB;
dexpr float Z1M2 = AM2 * partOfZ1inA + BM2 * partOfZ1inB;
dexpr float Z1M3 = AM3 * partOfZ1inA + BM3 * partOfZ1inB;
dexpr float Z2M1 = AM1 * partOfZ2inA + BM1 * partOfZ2inB;
dexpr float Z2M2 = AM2 * partOfZ2inA + BM2 * partOfZ2inB;
dexpr float Z2M3 = AM3 * partOfZ2inA + BM3 * partOfZ2inB;

//koszt ca³kowity (wartoœæ oczekiwana) = koszt produkcji + koszt sk³adowania komponentów
dexpr float totalCost = 
		(expectedValue[1] * AM1 + expectedValue[4] * BM1) * 
		(1 + month1Below100 * (AM1 + BM1) * 0.1 + month1Over100 * 10 + month1Over100 * (AM1 + BM1 - 100) * 0.15)
		+
		(expectedValue[2] * AM2 + expectedValue[5] * BM2) * 
		(1 + month2Below100 * (AM2 + BM2) * 0.1 + month2Over100 * 10 + month2Over100 * (AM2 + BM2 - 100) * 0.15)
		+
		(expectedValue[3] * AM3 + expectedValue[6] * BM3) * 
		(1 + month3Below100 * (AM3 + BM3) * 0.1 + month3Over100 * 10 + month3Over100 * (AM3 + BM3 - 100) * 0.15);

//koszt ca³kowity (scenariusza) = koszt produkcji + koszt sk³adowania komponentów
dexpr float scenarioCost[i in rangeScenario] = 
		(scenario[i][1] * AM1 + scenario[i][4] * BM1) * 
		(1 + month1Below100 * (AM1 + BM1) * 0.1 + month1Over100 * 10 + month1Over100 * (AM1 + BM1 - 100) * 0.15)
		+
		(scenario[i][2] * AM2 + scenario[i][5] * BM2) * 
		(1 + month2Below100 * (AM2 + BM2) * 0.1 + month2Over100 * 10 + month2Over100 * (AM2 + BM2 - 100) * 0.15)
		+
		(scenario[i][3] * AM3 + scenario[i][6] * BM3) * 
		(1 + month3Below100 * (AM3 + BM3) * 0.1 + month3Over100 * 10 + month3Over100 * (AM3 + BM3 - 100) * 0.15);

//œredni koszt - miara kosztu
dexpr float averageScenarioCost = 
		(1 / scenarioSize) * sum (i in rangeScenario) scenarioCost[i];

//ró¿nica Giniego
dexpr float giniCoefficient[i in rangeScenario] = 
		(1/2 * expectedValueSize * expectedValueSize) * 
		sum (j1 in rangeExpectedValue) sum (j2 in rangeExpectedValue) abs(scenario[i][j1] - scenario[i][j2]);

//œrednia ró¿nica Giniego - miara ryzyka
dexpr float averageGiniCoefficient = 
		(1 / scenarioSize) * sum(i in rangeScenario) giniCoefficient[i];

//************Metoda punktu odniesienia*********************
//indywidualna funkcja osi¹gniêcia minimum
dvar float individualAchieveFunction_minimum;

//indywidualna funkcja osi¹gniêcia dla kosztu
dvar float individualAchieveFunction_cost;

//indywidualna funkcja osi¹gniêcia dla ryzyka
dvar float individualAchieveFunction_risk;

maximize individualAchieveFunction_minimum + (individualAchieveFunction_cost + individualAchieveFunction_risk) * epsilon;

 //Ograniczenia (constraints)
 subject to
 {
   //ograniczenia z punktu 1 zadania
   AM1 + AM2 + AM3 == needA;
   BM1 + BM2 + BM3 == needB;
   
   //ograniczenia z punktu 5 zadania  
   Z1M1 <= posSupZ1M1;
   Z1M2 <= posSupZ1M2;
   Z1M3 <= posSupZ1M3;
   
   Z2M1 <= posSupZ2M1;
   Z2M2 <= posSupZ2M2;
   Z2M3 <= posSupZ2M3;
   
   //preferencje
   individualAchieveFunction_minimum <= individualAchieveFunction_cost;
   individualAchieveFunction_minimum <= individualAchieveFunction_risk;
   
   //????????????????????????
   individualAchieveFunction_cost <= beta * costLambda * (costAspiration - averageScenarioCost);
   individualAchieveFunction_cost <= costLambda * (costAspiration - totalCost);
   
   individualAchieveFunction_risk <= beta * riskLambda * (riskAspiration - averageGiniCoefficient);
   individualAchieveFunction_risk <= riskLambda * (riskAspiration - averageGiniCoefficient);
 
 };
    
    
   main
   {
    var outputFile = new IloOplOutputFile("wyniki.txt");
//  	 var fileRA = new IloOplOutputFile("risk.txt");
   
   	var model  = thisOplModel;
   	var definition  = model.modelDefinition;
   	var data = model.dataElements;

     
     
     outputFile.writeln("amtK1_F1;amtK1_F2;amtK1_M2;amtK2_F1;amtK2_M1;amtK2_M2;AvgCostAsp;RiskAsp;AvgCost;Risk;Solution");
   		data.asWhlRisk = 5;
    

  
  		file.close();   
     
   };   
   