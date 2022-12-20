open util / integer

//* * * Signatures * * *

sig CPO{
operator: some Operator,
mydso: one DSO,
}

sig Operator{
cpo: one CPO,
cs:some CS,
}

sig CS{
operator : one Operator,
cpo: one CPO,
dso: one DSO,
cp: some Point,
battery: set Battery,
}

sig DSO{
	cpo: some CPO,
}


sig Socket{}
sig Battery{cs: one CS}
sig Point{
socket: some Socket,
cs : one CS	
}

/* * * * FACTS * * * * */

//Every CS has one DSO from the same CPO
fact CStoDSOsameCPO{
all s:CS, c:CPO |
c in s.cpo implies s.dso = c.mydso
}

//Every Operator has only one CPO
fact oneOperatortoCPO{
all c1,c2:CPO, o:Operator |
o in c1.operator and o in c2.operator implies c1=c2
}

//Every DSO has only one CPO
fact oneOperatortoCPO{
all c1,c2:CPO, d:DSO |
d in c1.mydso and d in c2.mydso implies c1=c2
}

//Every CP has one and only one CS
fact operatorNoDuplicatesCS{
all c1,c2 : CS , p:Point |
p in c1.cp and p in c2.cp implies c1=c2
}
//Every Socket has one and only one CP
fact socketCP{
all p1,p2 : Point , s:Socket |
s in p1.socket and s in p2.socket implies p1=p2
}
//Every CP has one and only one CS
fact operatorNoDuplicatesCS{
all c1,c2 : CS , p:Point |
p in c1.cp and p in c2.cp implies c1=c2
}
//Every Battery has one and only one CS
fact batteriesInCS{
all c1,c2 : CS, b:Battery |
b in c1.battery and b in c2.battery implies c1 = c2
}



//Connection between Operator and CPO
fact connectionOperatortoCPO{
all o:Operator, c:CPO |
o in c.operator <=> c in o.cpo
}

/*
We have that: DSO can have more different CPOs, but every CPO has only one DSO and
every CS of the same  CPO has one DSO of the CPO
*/

// If we want that every CPO must have only one DSO and viceversa: uncomment this
/*
//Connection between DSO and CPO
fact connectionDSOandCPO{
all d:DSO, c:CPO |
d in c.dso<=> c in d.cpo
}
*/

//Connection between Operator and CS
fact connectionOperatortoCS{
all o:Operator, c:CS |
o in c.operator <=> c in o.cs
}

//Connection between CS and CPO of the same Operator
fact connectionCStoCPO{
all s:CS, o:Operator | 
s in o.cs and o in s.operator implies s.cpo = o.cpo
}

//Connection between Operator and CS
fact connectionPointToCS{
all c : CS, p : Point | c in p.cs <=> p in c.cp
}
//Connection between Operator and CS
fact connectionBatteriesCS{
all b:Battery | some c:CS | b in c.battery
}

//Connection between batteries and CS
fact batteryAndCS{
all b: Battery, c: CS | b in c.battery <=> c in b.cs
}

//There are CPs with at least one Socket
fact moreSocketInCP{
all p:Point | #p.socket >=2
}
//There are CS with more batteries
fact morebatteriesInCS{
all c:CS | #c.battery <=3
}

//* * * * * * * * * * Predicates* * * * * * * * * *
/*

pred show{
#CPO>=3
#Operator >=3
#CS >=4
}
run show for 30
*/
// For run the assertions, comment the Predicates and uncomment the assertion to check

//* * * * * * * * * * Assertions* * * * * * * * * *

/*
//Check if a CPO has more Operators
assert moreOperatorsInSameCPO{
all c:CPO, o1,o2:Operator |
o1 in c.operator and o2 in c.operator implies o1 = o2
}
check moreOperatorsInSameCPO for 10
*/

/*
//Check if a Operator has more CSs
assert moreCSsInSameOperator{
all o:Operator, s1,s2: CS |
s1 in o.cs and s2 in o.cs implies s1=s2
}
check moreCSsInSameOperator for 10
*/

//Check if a CPO has more DSO
assert moreDSOtoCPO{
all c1,c2 : CPO, d:DSO |
d in c1.mydso and d in c2.mydso implies c1=c2
}
check moreDSOtoCPO for 10





