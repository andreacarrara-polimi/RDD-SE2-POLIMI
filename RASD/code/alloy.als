
//SIGNATURES//

abstract sig Bool{}

sig True extends Bool{}

sig False extends Bool{}

abstract sig OutCome{}

sig Accepted, Rejected extends OutCome{}

abstract sig Mode{}

sig Remote, Onsite extends Mode{}

abstract sig ApplicationMode{}

sig Direct, Recommended extends ApplicationMode{}

abstract sig ApplicationStatus{}

sig ApplicationAccepted, ApplicationRejected extends ApplicationStatus{}

abstract sig Status{}

sig Ongoing, Finished extends Status{}


abstract sig User{
	email : one Email,
	password : one Password
}


sig Student extends User{
    name: one Name,
    surname: one Surname,
    cv: lone CV,
    applications : set Application,
    internships : set Internship,
    preferences: set Preference,
    university : one University,
    feedback: set Feedback
}


sig Company extends User{
	name : one Name,
	vat : one VatNumber,
	field : one Sector,
	description : lone Description,
	positions : set Position,
	feedback : set Feedback
}


sig University extends User{
	name : one Name,
	monitors : some Student,
}


sig Application{
	position : one Position, 
	student : one Student,
	mode : one ApplicationMode,
	status : one ApplicationStatus
}


sig Position{ 
	name : one Name,
	domain :  one Domain,
	project : some Project,
	task: some Task,
	acceptedStudents : set Student, 
	rejectedStudents : set Student,
	offeredBy : one Company,
	refersTo : one Internship,
	terms: some Term
}


sig Recommendation{ 
	recommendedStudent : one Student,
	studentAccepted : one Bool,
	companyAccepted: one Bool,
	recommendedPosition : one Position
}


sig Selection{ 
	status : one OutCome,
	connects : one Position, 
	refersTo: one Student,
	interview : set Interview,
	questionnaire : set Questionnaire
}


sig Interview{ 
	mode : one Mode,
	date: one Date
}


sig Internship{ 
	status : one Status,
	offeredBy : one Company,
	student : one Student,
	from : set Selection,
	comments : set Comment
}


sig Comment{
	wroteBy : one User,
	relatedTo: one Internship
} 


sig Feedback{
	wroteBy : one User 
}


sig Email {}

sig Password {}

sig Name {}

sig Surname {}

sig CV {}

sig Preference {}

sig Date{}

sig Domain {}

sig Project {}

sig Task {}

sig Term {}

sig Sector{}

sig Questionnaire{}

sig VatNumber{}

sig Description{}



--FACTS--


--All emails are unique 
fact UniqueEmail{
	no disj u1, u2 : User |
		u1.email = u2.email
}


-- All CVs are unique
fact UniqueCV{
	no disj s1,s2 : Student | 
		s1.cv = s2.cv
}


--Two distinct companies cannot share the same VAT number
fact UniqueVat{
	no disj c1, c2 : Company | 
		c1.vat = c2.vat
}


-- Two distinct universities cannot have the same name
fact UniqueUniversityName{
	no disj u1, u2 : University | 
		u1.name = u2.name
}


-- Students can't have the same name of a company or a university. Comapanies and universities can't have the same name
fact UniqueNames{
    all s: Student, c: Company | 
		s.name != c.name
    		all s: Student, u: University | 
				s.name != u.name
					all c: Company, u: University | 
						c.name != u.name
}


-- Two different universities can't have some students in common 
fact NoSharedStudentsBetweenUniversities{
    all u1, u2: University | 
        u1 != u2 implies #(u1.monitors & u2.monitors) =0
}


--An application is associated to only one student
fact UniqueApplicationPerStudent{
    all a: Application | 
		lone s: Student | 
			a in s.applications
}


--For a certain position and a student there's at most one application
fact UniqueApplicationPerStudentPosition{
    all s: Student, p: Position |
        lone a: Application | 
			a.student = s and a.position = p
}


--All positions listed in a student's internships are also in the student's applications
fact PositionsInInternshipsAreInApplications{
    all i: Internship | 
        all s: i.from | 
            some a: Application | 
                a.student = i.student and a.position = s.connects and s.refersTo=a.student
}


--A student can't have more than one ongoing internship 
fact OngoingInternship{
	all s: Student | 
		lone i: s.internships | 
			i.status = Ongoing
}


--A student is assigned to an internship if and only if that internship is part of the student's set of internships
fact StudentsHaveOnlyTheirInternships{
    all s: Student | 
        all i: Internship | 
            i.student = s iff i in s.internships
}


--A student is assigned to an application if and only if that application is part of the student's set 
fact ApplicationStudent{
all s: Student |	
	all a : Application |
		a.student=s iff a in s.applications
		
}


--If an application for a position is accepted that student must be in the set of the accepted ones for that position
fact ApplicationAcceptedAndAcceptedStudents{
    all a: Application |
         (a.status = ApplicationAccepted) iff (a.student in a.position.acceptedStudents)
}


--If an application for a position is rejected the student must be in the set of the rejected ones for that position
fact ApplicationRejectedAndRejectedStudents{
    all a: Application |
        (a.status = ApplicationRejected) iff (a.student in a.position.rejectedStudents)
}


--A student is listed in the students who applied for that position if there's an application filed by him for that position
fact ConsistentApplicationStatus{
    all s: Student, p: Position |
        (s in p.acceptedStudents or s in p.rejectedStudents) 
        	iff some a: s.applications | a.position = p
}


--In a position there cannot be a student both in the rejected ones and the accepted ones
fact NoDoubleStudent{
all p : Position |
	(p.acceptedStudents & p.rejectedStudents) = none
}


--There cannot be two equal positions
fact UniquePositions{
    all p1, p2: Position |
        p1 != p2 iff (p1.name != p2.name or 
                     p1.domain != p2.domain or 
                     p1.project != p2.project or 
                     p1.task != p2.task or 
                     p1.offeredBy != p2.offeredBy or
                     p1.refersTo != p2.refersTo)
}


--An application is direct if and only if there is no recommendation linking the same student and position
fact DirectApplicationCondition{
    all a: Application | 
        (a.mode = Direct) iff
        	(no r: Recommendation | 
				r.recommendedStudent = a.student and r.recommendedPosition = a.position)
}


--An application exists via recommendation if and only if there's a corresponding recommendation
fact DirectApplicationCondition{
    all a: Application | 
        (a.mode = Recommended) iff
        	(some r: Recommendation | 
				r.recommendedStudent = a.student and r.recommendedPosition = a.position)
}


-- A recommendation regarding a student and a position is unique
fact UniqueRecommendation{
    all r1, r2: Recommendation |
        r1 != r2 iff (r1.recommendedStudent != r2.recommendedStudent or
                     r1.recommendedPosition != r2.recommendedPosition or
                     r1.recommendedPosition.offeredBy != r2.recommendedPosition.offeredBy)
}


--An application is accepted as recommended if and only if there is a matching recommendation where both the student and company accepted
fact RecommendedAcceptedApplicationsMatchRecommendations{
    all a: Application | a.mode = Recommended and
		 a.status = ApplicationAccepted iff
        	(some r: Recommendation | 
            	r.recommendedStudent = a.student and 
            	r.recommendedPosition = a.position and 
            	r.studentAccepted = True and 
            	r.companyAccepted = True)
}


--An application is rejected as recommended if and only if there is a matching recommendation where either the student or the company, or both, did not accept
fact RecommendedRejectedApplicationsMatchRecommendations{
    all a: Application |
        (a.mode = Recommended and a.status = ApplicationRejected) iff
        	(some r: Recommendation | 
            	r.recommendedStudent = a.student and 
            	r.recommendedPosition = a.position and 
           	((r.studentAccepted = False and 
            	r.companyAccepted = True) or (r.studentAccepted=False and r.companyAccepted=False)  
				or (r.studentAccepted=True and r.companyAccepted=False)))
}


-- An accepted application for a position must have a corresponding selection process
fact ApplicationAcceptedCondition{
    all a: Application |
        (a.status = ApplicationAccepted) implies 
        	(one s: Selection | 
				s.refersTo = a.student and s.connects = a.position)
}


--A selection exists for an accepted application linking the student and position, while no selection process exists for a rejected application
fact SelectionExistsForAcceptedAndRejected{
    all a: Application |
        (a.status = ApplicationAccepted implies 
            (one s: Selection | 
                s.refersTo = a.student and 
                s.connects = a.position 
            )
        ) and
        (a.status = ApplicationRejected implies 
            no s: Selection | 
                s.refersTo = a.student and 
                s.connects = a.position
        )
}


--A selection exists only if it corresponds to an accepted application linking the same student and position.
fact SelectionExistsOnlyForAcceptedApplications{
    all s: Selection |
        some a: Application |
            a.student = s.refersTo and
            a.position = s.connects and
            a.status = ApplicationAccepted
}


--For each position and student there exists at most one selection process
fact UniqueSelectionForStudentPosition{
    all s: Student, p: Position |
        lone sel: Selection | 
			sel.refersTo = s and sel.connects = p
}


--For every position posted there must be at most one selection process that ends up with acceptance
fact SelectionConsistency{
	all p: Position | 
		lone s: Selection | 
			s.connects = p and s.status=Accepted
}


-- Each interview is associated with exactly one selection, and each questionnaire is associated with exactly one selection.
fact UniqueAssociation{
    all i: Interview | 
		one s: Selection | 
			i in s.interview
    all q: Questionnaire | 
		one s: Selection | 
			q in s.questionnaire
}


--All interviews need to have different dates
fact InterviewDates{
	all disj i1,i2: Interview |
		i1.date!=i2.date
}


--An internship exists for a student if and only if there is an accepted selection linking the student and a position offered by the internship's company
fact InternshipExistsIfSelectionAccepted{
    all i: Internship | 
        (some s: Selection | 
            s.connects in i.offeredBy.positions and 
            s.refersTo = i.student and 
            s.status = Accepted
        ) iff i in i.student.internships
}


--For each position there's only one internship related
fact UniqueInternshipPerPosition{
    all p1, p2: Position | 
		p1 != p2 iff p1.refersTo != p2.refersTo
}


--There cannot be two equal internships 
fact UniqueInternship{
    all disj i1, i2: Internship |
        i1.student != i2.student or
        i1.offeredBy != i2.offeredBy or
        i1.from != i2.from
}


--No two internships can involve the same student and the same position simultaneously
fact UniqueInternshipPerStudentAndPosition{
    all i1, i2: Internship |
        i1 != i2 implies (i1.student != i2.student or i1.refersTo != i2.refersTo)
}


--A student is monitored by his university only if he has an internship in his profile
fact StudentMonitorsCondition{
    all u: University, s: Student |
        s in u.monitors iff
        (s.university = u and some i: Internship | i.student = s)
}


--Each comment is related to at most one internship
fact CommentsRelateToAtMostOneInternship{
    all c: Comment | 
        lone i: Internship | 
			c.relatedTo = i
}


--Students can publish comments only regarding their own internships
fact StudentsCanOnlyCommentOnTheirOwnInternships{
    all c: Comment | 
        c.wroteBy in Student implies 
        c.relatedTo in c.wroteBy.internships
}


--Companies can publish comments only regarding their own internships
fact CompanyCommentsOnProvidedInternships{
    all c: Comment | 
        c.wroteBy in Company implies 
        (c.relatedTo.offeredBy = c.wroteBy)
}


--Universities can publish comments only regarding their students' internships
fact UniversityCommentsOnMonitoredInternships{
	all u: University, c: Comment |
		c.wroteBy = u implies 
			c.relatedTo.student in u.monitors
}


--Every internship contain all and only the comments related to it
fact InternshipsContainOnlyTheirComments{
    all i: Internship | 
        i.comments = {c: Comment | c.relatedTo = i}
}


-- The author of a feedback must be a student or a company
fact FeedbackAuthor{
	all f: Feedback | 
		f.wroteBy in Student + Company 
}


--All companies have in the list of feedback all and only the ones wrote by them 
fact CompanyHaveOnlyTheirFeedback{
    all c: Company |
        c.feedback = {f: Feedback | f.wroteBy = c}
}


--All students have in the list of feedback all and only the ones wrote by them 
fact StudentHaveOnlyTheirFeedback{
    all s: Student |
        s.feedback = {f: Feedback | f.wroteBy = s}
}


--ASSERTIONS--

assert noUserHasSameEmail{
	all u1, u2 : User | 
		u1!=u2 implies u1.email!=u2.email
}

check noUserHasSameEmail for 5


assert noStudentHasSameCv{
	all s1, s2 : Student | 
		s1!=s2 implies s1.cv != s2.cv
}

check noStudentHasSameCv for 5


assert NoDupRecommendation {
    all r1, r2: Recommendation |
        r1 != r2 implies 
            (r1.recommendedStudent != r2.recommendedStudent or
             r1.recommendedPosition != r2.recommendedPosition or
             r1.recommendedPosition.offeredBy != r2.recommendedPosition.offeredBy)
}

check NoDupRecommendation for 5 


assert PositionsInInternshipsAreInApplications {
    all i: Internship | 
        all s: i.from | 
            some a: Application | 
                a.student = i.student and 
                a.position = s.connects and 
                s.refersTo = a.student
}

check PositionsInInternshipsAreInApplications for 5 


assert uniqueAppForStudentPosition {
	all s: Student | 
		all a1,a2 : s.applications|
	 		a1.position != a2.position implies  a1!=a2 
}

check uniqueAppForStudentPosition for 5


assert noRepeatedStudent {
	all p : Position | 
		(no s: Student | s in p.acceptedStudents and s in p.rejectedStudents)

}

check noRepeatedStudent for 5


assert ApplicationAcceptedCorrectly{
	all a : Application | 
		(a.status = ApplicationAccepted) implies (a.student in a.position.acceptedStudents)
}

check ApplicationAcceptedCorrectly for 5


assert ApplicationRejectedCorrectly {
    all a: Application |
         (a.student in a.position.rejectedStudents) implies (a.status = ApplicationRejected)
}

check ApplicationRejectedCorrectly for 5


assert ApplicationAcceptedselection {
    all a: Application |
        ((a.status = ApplicationAccepted) implies 
        (one s: Selection | s.refersTo = a.student and s.connects = a.position)) and ((one s: Selection | s.refersTo = a.student and s.connects = a.position)  implies (a.status = ApplicationAccepted))
}

check ApplicationAcceptedselection for 5


assert UniqueInternship{
	all s: Student | no disj i1, i2 : s.internships | 
 		i1.status=Ongoing and i2.status=Ongoing

}
check UniqueInternship for 5


assert NoDuplicateApplicationsForStudent {
    all s: Student |
        all disj a1, a2: s.applications |
            a1.position != a2.position
}

check NoDuplicateApplicationsForStudent for 5


assert SelectionRequiresCorrespondingApplication {
    all s: Selection |
        some a: s.refersTo.applications | 
            a.position = s.connects
}

check SelectionRequiresCorrespondingApplication for 5


--Base world: 2 students, 1 company, 1 position. Both students apply, one through recommendation. Only one students obtains the internship.

pred BaseWorld {
	#Company =1
	#Student= 2
	#Position = 1
	#Application =2
	#Selection =1
	#Recommendation=1
	#Internship=1
}

run BaseWorld for 4



