//do not specify standard types like string

sig UserLoginCredentials{ //contains email and password
}

sig UserPersonalnformation{
}

abstract sig User{
	userInformation : UserPersonalnformation,
	credentials : UserLoginCredentials
}

sig CompanyMember extends User{
	employedAtCompany: Company
}

sig UniversityMember extends User{
	employedAtUniversity: University
}

sig Student extends User{
	enrolled: University
}

sig UniversityInformation{
}

sig University{
	universityInformation: UniversityInformation,
	universityMailDomain: MailDomain,
}{ some member : UniversityMember | this in member.employedAtUniversity }


sig CompanyInformation{
}

sig MailDomain{
}

sig Company{
	companyInformation: CompanyInformation,
	companyMailDomain: MailDomain,
}{ some member : CompanyMember | this in member.employedAtCompany }

sig Internship{
	offered: Company,
	description: InternshipDescription,
	var candidatureStatus: CandidaturesStatus
}

enum CandidaturesStatus{ Closed, Open } //when open the internship can receive request, closed when it doesn't accept requests anymore

sig InternshipDescription{
}

sig Request{
	var requestStatus: RequestStatus,
	internshipReferred: Internship,
	requestedBy: User,
	requestedTo: User //relation 0 ..* for the user => no need to add a constraint
}

enum RequestStatus{ Pending, Approved, Declined }

//internship availability

pred internshipApplicationAvailability[ i : Internship]{
	i.candidatureStatus = Open
}

pred closeApplicationAvailability[ i : Internship]{
	i.candidatureStatus = Open and i.candidatureStatus' = Closed
}

pred openApplicationAvailability[ i : Internship]{ //oss the internship can be published also already opened
	i.candidatureStatus = Closed and i.candidatureStatus' = Open
}

fact applicationAvailabilityAfterClosure{
	all i : Internship | always ( ( i.candidatureStatus = Closed and once closeApplicationAvailability[ i ] ) implies i.candidatureStatus' = Closed )
}

fact applicationAvailabilityBeforeOpening{
	all i : Internship | always ( ( historically  i.candidatureStatus = Closed ) implies ( eventually  i.candidatureStatus = Open ))
}

fact applicationAvailabilityAfterOpening{
	all i : Internship | always (  i.candidatureStatus = Open implies eventually  i.candidatureStatus = Closed)
}


//are internship unique? if yes we need an ID

fact credentialsIdentifyUsers{
	no disj u1, u2 : User | u1.credentials = u2.credentials
}

//companies and universities identified by domain 

fact mailDomainIdentifiesCompanies{
	no disj c1, c2 : Company | c1.companyMailDomain = c2.companyMailDomain
}

fact mailDomainIdentifiesUniversities{
	no disj u1, u2 : University | u1.universityMailDomain = u2.universityMailDomain
}

//request fact

pred declineRequest[ r : Request ]{
	r.requestStatus = Pending
	r.requestStatus' = Declined
}

pred approveRequest[ r : Request ]{
	r.requestStatus = Pending
	r.requestStatus' = Approved
}


fact pendingRequestBehaviour{
	all r : Request | always ( r.requestStatus = Pending implies ((eventually  declineRequest[ r ] ) or (eventually  approveRequest[ r ]) and (historically r.requestStatus = Pending)))	
}

fact requestAreEvaluatedOnlyOneTime{
	all r : Request | always ( r.requestStatus != Pending implies r.requestStatus' = r.requestStatus)
}

fact evaluatedRequestWerePending{
	 all r : Request | always ( r.requestStatus != Pending implies once r.requestStatus = Pending)
}

fact usersCannotSendRequestToThemselves{
	all r : Request | r.requestedBy != r.requestedTo
}

fact noDuplicateRequests{
	all disj r1, r2 : Request | (r1.requestedBy != r2.requestedBy) or (r1.internshipReferred != r2.internshipReferred)
}

fact userRolesConstraints{ //avoid also university member as user
	all r : Request | #(( r.requestedBy + r.requestedTo ) & Student) = 1 and #((r.requestedBy + r.requestedTo ) & CompanyMember) = 1
}


//functions


fun companyMembersEmployed[ c : Company ] : some CompanyMember{
	{ m : CompanyMember | m.employedAtCompany = c }
}

fun universityMembersEmployed[ u : University ] : some UniversityMember{
	{ m : UniversityMember | m.employedAtUniversity = u }
}

fun studentsEnrolled[ u : University ] : set Student{
	{ s : Student | s.enrolled = u }
}

fact {
  some Request
}

pred show{}

run show for 50 but 5 Request, 5 User

//4h



















