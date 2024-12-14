----------------------------------------------------------------------
-- SIGNATURES
----------------------------------------------------------------------

-- USER


abstract sig User{
	userInformation : UserPersonallnformation,
	credentials : UserLoginCredentials
}


-- Contains the user's email and password.

sig UserLoginCredentials{ }

sig UserPersonallnformation{ }

sig CompanyMember extends User{
	employedAtCompany: Company
}

sig UniversityMember extends User{
	employedAtUniversity: University
}

sig Student extends User{
	enrolled: University
}


-- GROUP OF USERS


-- In order to be created, a University must have at least one member.

sig University{
	universityInformation: UniversityInformation,
	universityMailDomain: MailDomain,
}{ some member : UniversityMember | this in member.employedAtUniversity } 


-- Contains university information, such as its name.

sig UniversityInformation{
}


-- In order to be created, a Company must have at least one member.

sig Company{
	companyInformation: CompanyInformation,
	companyMailDomain: MailDomain,
}{ some member : CompanyMember | this in member.employedAtCompany }


-- Contains company information, such as its name and a description.

sig CompanyInformation{ }


-- Represents the email domain of a company or university and identifies them.

sig MailDomain{ }


-- INTERNSHIP


sig Internship{ 
	id : InternshipId,
	offered: Company,
	description: InternshipDescription,
	var candidatureStatus: CandidaturesStatus
}


-- Represents an ID used to distinguish between different internship offers.

sig InternshipId { }


-- Defines the interval during which applications for a specific internship can be submitted. According to the class diagram attributes,
-- the internship will have a status of 'Open' between the applicationStartDate and applicationEndDate, and 'Closed' at all other times.

enum CandidaturesStatus{ Closed, Open } 


-- Contains all information related to the internship offer, including the name, terms, and duration.

sig InternshipDescription{ }


--REQUEST


-- This signature is dynamic over time, as different requests can be sent at different moments.

var sig Request{
	var requestStatus: RequestStatus,
	var internshipReferred: Internship,
	var requestedBy: User,
	var requestedTo: User
}

enum RequestStatus{ Pending, Approved, Declined }



----------------------------------------------------------------------
-- PREDICATES
----------------------------------------------------------------------


-- The predicate is true when the internship is open for receiving applications.

pred internshipOpenForApplications[ i : Internship ]{
	i.candidatureStatus = Open
}


-- The predicate models the closure of an internship period for receiving applications.

pred closeApplicationAvailability[ i : Internship ]{
	i.candidatureStatus = Open and i.candidatureStatus' = Closed
}


-- The predicate models the opening of an internship period for receiving applications (the internship may also be published as already open).

pred openApplicationAvailability[ i : Internship ]{
	i.candidatureStatus = Closed and i.candidatureStatus' = Open
}


-- The predicate models the rejection of a pending request.

pred declineRequest[ r : Request ]{
	r.requestStatus = Pending
	r.requestStatus' = Declined
}


-- The predicate models the approval of a pending request.

pred approveRequest[ r : Request ]{
	r.requestStatus = Pending
	r.requestStatus' = Approved
}


-- The predicate represents the addition of a new request to the model. 

pred addNewRequest [ sender , receiver : User , internship : Internship ]{

	//precondition

	internship in Internship
	sender in (Student + CompanyMember) 
	receiver in (Student + CompanyMember)
	( ( sender in Student ) implies ( receiver in CompanyMember ) )
	( ( sender in CompanyMember ) implies ( receiver in CompanyMember ) )

	//postcondition

	( no r : Request | 
		r.internshipReferred = internship and 
		r.requestedBy = sender and 
		r.requestedTo = receiver )
	( after ( 
		one r : Request | 
			r.internshipReferred = internship and 
			r.requestedBy = sender and 
			r.requestedTo = receiver and 
			r.requestStatus = Pending ) //say redundant
	)

}



----------------------------------------------------------------------
-- FACTS
----------------------------------------------------------------------


-- For all internships, once the period for accepting applications ends, it cannot be reopened.

fact applicationAvailabilityAfterClosure{
	all i : Internship | 
		always ( 
			( i.candidatureStatus = Closed and once closeApplicationAvailability[ i ] ) 
				implies i.candidatureStatus' = Closed 
		)
}


-- Every internship that has never been available for receiving applications will eventually enter a period of availability.

fact applicationAvailabilityBeforeOpening{
	all i : Internship | 
		always ( 
			( historically  i.candidatureStatus = Closed )
				implies ( eventually  i.candidatureStatus = Open ) 
		)
}


-- Every internship's period of availability for receiving applications will eventually end.

fact applicationAvailabilityAfterOpening{
	all i : Internship | 
		always ( 
			( i.candidatureStatus = Open ) 
				implies ( eventually  i.candidatureStatus = Closed ) 
		)
}


-- There are not two instances of the same internship offer

fact credentialsIdentifyUsers{
	no disj u1, u2 : User |
		 u1.credentials = u2.credentials
}


-- There are not two instances of the same Company

fact mailDomainIdentifiesCompanies{
	no disj c1, c2 : Company | 
		c1.companyMailDomain = c2.companyMailDomain
}


-- There are not two instances of the same University

fact mailDomainIdentifiesUniversities{
	no disj u1, u2 : University | 
		u1.universityMailDomain = u2.universityMailDomain
}


-- There are not common email domain between universities and companies

fact noCompanySharesMailDomainWithUniversity{
	no c : Company , u : University | 
		c.companyMailDomain = u.universityMailDomain
}


-- Every pending request will eventually be evaluated.

fact pendingRequestBehaviour{
	always ( 
		all r : Request |  
			r.requestStatus = Pending 
				implies ( ( ( eventually  declineRequest[ r ] ) or ( eventually  approveRequest[ r ] ) ) ) 
	)	
}


-- An evaluated request cannot be evaluated again or return pending.

fact requestAreEvaluatedOnlyOneTime{
	always ( 
		all r : Request |  
			r.requestStatus != Pending 
				implies r.requestStatus' = r.requestStatus
	)
}


-- All the evaluated request were once pending. //redundant

fact evaluatedRequestWerePending{
	always ( 
		all r : Request | 
			r.requestStatus != Pending 
				implies once r.requestStatus = Pending)
}


-- There cannot be a Request which sender is also the receiver.

fact usersCannotSendRequestToThemselves{
	always ( 
		all r : Request | 
			r.requestedBy != r.requestedTo 
	)
}


-- There are not duplicate requests.

fact noDuplicateRequests{
	always ( 
		all disj r1, r2 : Request | 
			(r1.requestedBy != r2.requestedBy) or (r1.internshipReferred != r2.internshipReferred) )
}


-- The sender and receiver must always be either a Student and a CompanyMember, or a CompanyMember and a Student.

fact userRolesConstraints{ 
	always (
		 all r : Request | 
			# ( ( r.requestedBy + r.requestedTo ) & Student ) = 1 and
			# ( ( r.requestedBy + r.requestedTo ) & CompanyMember ) = 1
	)
}


-- There are not duplicate internship offers

fact noDuplicateInternship{
	no disj i1, i2 : Internship | i1.id = i2.id
}


-- The Request signature is dynamic, but the fields "internshipReferred", "requestedBy", and "requestedTo" of a specific request 
-- do not change over time once assigned.

fact requestFieldsDoesNotChange{
	always (
		all r : Request | 
			r.internshipReferred' = r.internshipReferred and 
			r.requestedBy' =  r.requestedBy and 
			r.requestedTo' = r.requestedTo
	)
}


-- All requests sent by students are evaluated after the application period terminates, once the company has received all possible applications. 
-- If a company member sent the request to a student, the student has no constraint on when to evaluate the request.

fact requestEvaluatedAfterClosure{
	always( 
		all r : Request | 
			( r.requestStatus != Pending and 
			  r.requestedBy in Student )	
				implies r.internshipReferred.candidatureStatus = Closed
	)
}


-- It is not possible to have a request related to an internship that has not started its period of availability for receiving applications. 
-- Requests begin to arrive only after the period starts.

fact requestCannotReferInternshipsBeforeOpening{
	always( 
		all r : Request | 
			r.internshipReferred.candidatureStatus = Closed
				implies ( once  closeApplicationAvailability[ r.internshipReferred ] ) 
	)
}


-- Every Request has been added to the model once

fact allRequestHaveBeenOnceSent{
	always ( 
		all r : Request | 
			( once ( not r in Request ) ) and 
			( once ( addNewRequest [ r.requestedBy, r.requestedTo, r.internshipReferred ] ) ) 
		)
	
}



----------------------------------------------------------------------
-- FUNCTIONS
----------------------------------------------------------------------


-- Returns all the company members of a Company "c".

fun companyMembersEmployed[ c : Company ] : some CompanyMember{
	{ m : CompanyMember | m.employedAtCompany = c }
}


-- Returns all the university members of a University "u",

fun universityMembersEmployed[ u : University ] : some UniversityMember{
	{ m : UniversityMember | m.employedAtUniversity = u }
}



-- Returns all the students of a University "u".

fun studentsEnrolled[ u : University ] : set Student{
	{ s : Student | s.enrolled = u }
}



----------------------------------------------------------------------
-- RUN EXAMPLES
----------------------------------------------------------------------



pred show1 {
	#Request' = 2
	#Internship = 2
	#Company = 2 
	#University = 1
	#Student = 2
	#CompanyMember = 2
}

pred show2 {
	( some c1, c2 : User, i : Internship | eventually addNewRequest[ c1, c2, i ] )
	eventually ( some r1, r2 : Request | r1.requestStatus = Approved and r2.requestStatus = Declined )
	#Internship > 2
	#Company = 2 
	#University = 2
	( some i : Internship | i.candidatureStatus = Closed )
} 

run show1 for 10 
