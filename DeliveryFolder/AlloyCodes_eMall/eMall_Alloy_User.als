open util / integer

// * * * * * * * * * * Signatures * * * * * * * * * * 

sig CF{}
sig OperatorID{}
sig Email{}
sig BusinessEmail{}
sig Password{}

sig Coordinates{
	coordinates: some User,
}

abstract sig User{
	coordinates : one Coordinates,
}

sig Driver extends User{
	cf: one CF,
	email : one Email,
	password : one Password,
}

sig Operator extends User{
	operatorID : one OperatorID,
	businessEmail : one BusinessEmail,
	password : one Password,
}

// * * * * * * * * * * Facts * * * * * * * * * * 

//There are no CFs duplicates (each Driver can register just once)
fact CFNODuplicates{
all d1,d2: Driver, thiscf: CF |
thiscf in d1.cf and thiscf in d2.cf implies d1 = d2
}

//There are no email duplicates(each Driver can register just once)
fact EmailNODuplicates{
all d1,d2: Driver, thisemail:  Email |
thisemail in d1.email and thisemail in d2.email implies d1 = d2
}

//There are no OpertorID duplicates
fact OperatorIDNoDuplicate{
all o1,o2: Operator, thisid : OperatorID |
thisid in o1.operatorID and thisid in o2.operatorID implies o1 = o2
}

//There are no business email addresses duplicates
fact BusinessAddressNODuplicates{
all o1,o2: Operator, thisbe:  BusinessEmail |
thisbe in o1.businessEmail and thisbe in o2.businessEmail implies o1 = o2
}

//All OperatorIDs have to be associated to an Operator
fact IDOperatorConnection{
all id : OperatorID | some o:Operator | id in o.operatorID
}

//All business email address have to be associated to an Operator
fact BusinessEmailOperatorConnection{
all bemail : BusinessEmail | some o:Operator | bemail in o.businessEmail
}

//All CFs have to be associated to a Operator
fact CFDriverConnection{
all c: CF | some d: Driver | c in d.cf 
}

//All Email Address have to be associated to an Operator
fact EmailDriverConnection{
all e : Email | some d:Driver | e in d.email
}

//All Password have to be associated to a Driver
fact PasswordDriverConnection{
all p:Password | some d:Driver | p in d.password
}


//All Password have to be associated to a Operator
fact PasswordOperatorConnection{
all p:Password | some o:Operator | p in o.password
}


//Coordinates have one or more Users, and User has only one coordinates
fact MoreUsersCoordinates{
all c : User , u: Coordinates | c in u.coordinates <=> u in c. coordinates
}


//* * * * * * * * * * Predicates* * * * * * * * * *

pred show{
#Operator >=2
#Driver >=2
}

run show for 5




