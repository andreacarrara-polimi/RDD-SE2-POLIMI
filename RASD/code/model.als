-- SIGNATURES

sig Email {}

sig Password {}

abstract sig User {
  email: one Email,
  password: one Password
}

sig Name {}

sig Surname {}

sig CV {}

sig Preference {}

sig Student extends User {
  name: one Name,
  surname: one Surname,
  cv: lone CV,
  preferences: set Preference,
  university: one University,
  applications: set Application,
  internships: set Internship,
  feedbacks: set Feedback
}

sig Field {}

sig Company extends User {
  name: one Name,
  field: one Field,
  positions: set Position,
  feedback: set Feedback
}

sig University extends User {
  name: one Name,
  students: some Student
}

sig Domain {}

sig Project {}

sig Task {}

sig Term {}

sig Position {
  name: one Name,
  domain: one Domain,
  project: some Project,
  tasks: some Task,
  terms: some Term,
  company: one Company,
  acceptedStudents: set Student,
  rejectedStudents: set Student,
  internship: one Internship
}

abstract sig ApplicationMode {}

sig Direct, Recommended extends ApplicationMode {}

abstract sig ApplicationStatus {}

sig ApplicationAccepted, ApplicationRejected extends ApplicationStatus {}

sig Application {
  status: one ApplicationStatus,
  mode: one ApplicationMode,
  position: one Position,
  student: one Student
}

abstract sig Bool {}

sig True, False extends Bool {}

sig Recommendation {
  studentAccepted: one Bool,
  companyAccepted: one Bool,
  student: one Student,
  position: one Position
}

sig Questionnaire {}

abstract sig SelectionOutcome {}

sig Accepted, Rejected extends SelectionOutcome {}

sig Selection {
  outcome: one SelectionOutcome,
  position: one Position,
  student: one Student,
  interviews: set Interview,
  questionnaires: set Questionnaire
}

abstract sig InterviewMode {}

sig Remote, Onsite extends InterviewMode {}

sig Date {}

sig Interview {
  date: one Date,
  mode: one InterviewMode
}

abstract sig InternshipStatus {}

sig Ongoing, Finished extends InternshipStatus {}

sig Internship {
  status: one InternshipStatus,
  company: one Company,
  student: one Student,
  selection: set Selection,
  comments: set Comment
}

sig Comment {
  internship: one Internship,
  user: one User
}

sig Feedback {
  user: one User
}

-- FACTS 

-- All emails are unique
fact EmailsAreUnique {
  no disj u1, u2: User |
    u1.email = u2.email
}

-- All CVs are unique
fact StudentCVsAreUnique {
  no disj s1, s2: Student |
    s1.cv = s2.cv
}

-- Two distinct universities cannot have the same name
fact UniversityNamesAreUnique {
  no disj u1, u2: University |
    u1.name = u2.name
}

-- Students, companies, and universities cannot share the same name
fact EntityNamesAreDistinct {
  all s: Student, c: Company |
    s.name != c.name
  all s: Student, u: University |
    s.name != u.name
  all c: Company, u: University |
    c.name != u.name
}

-- Two different universities cannot have students in common
fact UniversitiesDoNotShareStudents {
  all u1, u2: University |
    u1 != u2 implies #(u1.students & u2.students) = 0
}

-- An application belongs to only one student
fact ApplicationHasSingleOwner {
  all a: Application |
    lone s: Student |
      a in s.applications
}

-- For each (student, position) pair, there is at most one application
fact UniqueApplicationPerStudentPosition {
  all s: Student, p: Position |
    lone a: Application |
      a.student = s and a.position = p
}

-- All positions in a student's internship selections appear in the student's applications
fact PositionsInInternshipsAreInApplications {
  all i: Internship |
    all sel: i.selection |
      some a: Application |
        a.student = i.student
        and a.position = sel.position
        and sel.student = a.student
}

-- A student can have at most one ongoing internship
fact SingleOngoingInternship {
  all s: Student |
    lone i: s.internships |
      i.status = Ongoing
}

-- A student's internships must match the internships listing that student
fact StudentsHaveOnlyTheirInternships {
  all s: Student |
    all i: Internship |
      i.student = s iff i in s.internships
}

-- A student's applications must match the applications listing that student
fact StudentApplicationsAreConsistent {
  all s: Student |
    all a: Application |
      a.student = s iff a in s.applications
}

--If an application for a position is accepted that student must be in the set of the accepted ones for that position
fact AcceptedApplicationsMatchAcceptedSets {
  all a: Application |
    (a.status = ApplicationAccepted) iff (a.student in a.position.acceptedStudents)
}

--If an application for a position is rejected the student must be in the set of the rejected ones for that position
fact RejectedApplicationsMatchRejectedSets {
  all a: Application |
    (a.status = ApplicationRejected) iff (a.student in a.position.rejectedStudents)
}

-- If a student is in a position’s accepted or rejected set, that student must have applied
fact ConsistentApplicationStatus {
  all s: Student, p: Position |
    (s in p.acceptedStudents or s in p.rejectedStudents)
    iff some a: s.applications | a.position = p
}

-- No position may list the same student in both accepted and rejected sets
fact PositionAcceptedAndRejectedSetsAreDisjoint {
  all p: Position |
    (p.acceptedStudents & p.rejectedStudents) = none
}

-- Positions are unique by at least one differing field
fact UniquePositions {
  all p1, p2: Position |
    p1 != p2 iff (
      p1.name != p2.name or
      p1.domain != p2.domain or
      p1.project != p2.project or
      p1.tasks != p2.tasks or
      p1.company != p2.company or
      p1.internship != p2.internship
    )
}

-- A direct application exists iff there is no matching recommendation
fact DirectApplicationsHaveNoRecommendations {
  all a: Application |
    (a.mode = Direct) iff
      no r: Recommendation |
        r.student = a.student and r.position = a.position
}

-- A recommended application exists iff there is a matching recommendation
fact RecommendedApplicationsHaveRecommendations {
  all a: Application |
    (a.mode = Recommended) iff
      some r: Recommendation |
        r.student = a.student and r.position = a.position
}

-- Each (student, position) recommendation is unique
fact RecommendationsAreUnique {
  all r1, r2: Recommendation |
    r1 != r2 iff (
      r1.student != r2.student or
      r1.position != r2.position or
      r1.position.company != r2.position.company
    )
}

-- A recommended and accepted application matches a recommendation where both student and company accepted
fact AcceptedRecommendedApplicationsMatchRecommendations {
  all a: Application |
    a.mode = Recommended and a.status = ApplicationAccepted iff
      some r: Recommendation |
        r.student = a.student
        and r.position = a.position
        and r.studentAccepted = True
        and r.companyAccepted = True
}

-- A recommended and rejected application matches a recommendation where student or company (or both) did not accept
fact RejectedRecommendedApplicationsMatchRecommendations {
  all a: Application |
    (a.mode = Recommended and a.status = ApplicationRejected) iff
      some r: Recommendation |
        r.student = a.student
        and r.position = a.position
        and (
          (r.studentAccepted = False and r.companyAccepted = True) or
          (r.studentAccepted = False and r.companyAccepted = False) or
          (r.studentAccepted = True and r.companyAccepted = False)
        )
}

-- An accepted application must have a corresponding selection
fact AcceptedApplicationsRequireSelection {
  all a: Application |
    (a.status = ApplicationAccepted) implies
      one s: Selection |
        s.student = a.student and s.position = a.position
}

-- Accepted applications must have one selection; rejected applications have none
fact AcceptedAppsHaveSelectionsRejectedAppsHaveNone {
  all a: Application |
    (a.status = ApplicationAccepted implies
      one s: Selection |
        s.student = a.student and s.position = a.position
    )
    and
    (a.status = ApplicationRejected implies
      no s: Selection |
        s.student = a.student and s.position = a.position
    )
}

-- Selections exist only for accepted applications
fact SelectionExistsOnlyForAcceptedApplications {
  all s: Selection |
    some a: Application |
      a.student = s.student
      and a.position = s.position
      and a.status = ApplicationAccepted
}

-- For each (student, position) pair, there is at most one selection
fact UniqueSelectionForStudentPosition {
  all s: Student, p: Position |
    lone sel: Selection |
      sel.student = s and sel.position = p
}

-- For each position, at most one selection that ends with a positive outcome
fact SelectionConsistency {
  all p: Position |
    lone s: Selection |
      s.position = p and s.outcome = Accepted
}

-- Each interview and questionnaire belongs to exactly one selection
fact InterviewsAndQuestionnairesHaveUniqueAssociations {
  all i: Interview |
    one s: Selection |
      i in s.interviews
  all q: Questionnaire |
    one s: Selection |
      q in s.questionnaires
}

-- All interviews have different dates
fact InterviewDatesAreUnique {
  all disj i1, i2: Interview |
    i1.date != i2.date
}

-- An internship exists iff there is an accepted selection for the same student and a position from that company
fact InternshipExistsIfSelectionAccepted {
  all i: Internship |
    (some s: Selection |
      s.position in i.company.positions
      and s.student = i.student
      and s.outcome = Accepted
    ) iff i in i.student.internships
}

-- Each position has exactly one corresponding internship
fact SingleInternshipPerPosition {
  all p1, p2: Position |
    p1 != p2 iff p1.internship != p2.internship
}

-- No two internships are identical in student, company, or selection
fact InternshipsAreUnique {
  all disj i1, i2: Internship |
    i1.student != i2.student
    or i1.company != i2.company
    or i1.selection != i2.selection
}

-- No two internships can involve the same student for the same position
fact UniqueInternshipPerStudentAndPosition {
  all i1, i2: Internship |
    i1 != i2 implies (
      i1.student != i2.student or
      no p: Position |
        (some s1: i1.selection | s1.position = p)
        and (some s2: i2.selection | s2.position = p)
    )
}

-- A university lists a student only if that student actually belongs to it and has an ongoing internship
fact StudentMonitorsCondition {
  all u: University, s: Student |
    s in u.students iff
      (s.university = u and some i: Internship | i.student = s)
}

-- Each comment relates to exactly one internship
fact CommentsRelateToAtMostOneInternship {
  all c: Comment |
    lone i: Internship |
      c.internship = i
}

-- Students can only comment on their own internships
fact StudentsCanOnlyCommentOnTheirOwnInternships {
  all c: Comment |
    c.user in Student implies
      c.internship in c.user.internships
}

-- Companies can only comment on internships they provide
fact CompanyCommentsOnProvidedInternships {
  all c: Comment |
    c.user in Company implies
      c.internship.company = c.user
}

-- Universities can only comment on internships of their students
fact UniversityCommentsOnMonitoredInternships {
  all u: University, c: Comment |
    c.user = u implies
      c.internship.student in u.students
}

-- Internships contain all and only the comments related to them
fact InternshipsContainOnlyTheirComments {
  all i: Internship |
    i.comments = {c: Comment | c.internship = i}
}

-- The author of a feedback is either a student or a company
fact FeedbackAuthor {
  all f: Feedback |
    f.user in Student + Company
}

-- Companies list all and only their feedback
fact CompanyHaveOnlyTheirFeedback {
  all co: Company |
    co.feedback = {f: Feedback | f.user = co}
}

-- Students list all and only their feedback
fact StudentHaveOnlyTheirFeedback {
  all s: Student |
    s.feedbacks = {f: Feedback | f.user = s}
}


-- ASSERTIONS --

assert NoDuplicateEmails {
  all u1, u2: User |
    u1 != u2 implies u1.email != u2.email
}
check NoDuplicateEmails for 5

assert NoDuplicateCVs {
  all s1, s2: Student |
    s1 != s2 implies s1.cv != s2.cv
}
check NoDuplicateCVs for 5

assert NoDuplicateRecommendations {
  all r1, r2: Recommendation |
    r1 != r2 implies (
      r1.student != r2.student or
      r1.position != r2.position or
      r1.position.company != r2.position.company
    )
}
check NoDuplicateRecommendations for 5

assert NoDuplicateApplications {
  all s: Student |
    all disj a1, a2: s.applications |
      a1.position != a2.position
}
check NoDuplicateApplications for 5

assert SelectionsMatchApplications {
  all sel: Selection |
    some a: sel.student.applications |
      a.position = sel.position
}
check SelectionsMatchApplications for 5

assert NoDuplicatePositionsOutcome {
  all p: Position |
    no s: Student |
      s in p.acceptedStudents and s in p.rejectedStudents
}
check NoDuplicatePositionsOutcome for 5

assert ApplicationsAcceptedMatchPositionsOutcome {
  all a: Application |
    (a.status = ApplicationAccepted) implies
      a.student in a.position.acceptedStudents
}
check ApplicationsAcceptedMatchPositionsOutcome for 5

assert ApplicationsRejectedMatchPositionsOutcome {
  all a: Application |
    (a.status = ApplicationRejected) implies
      a.student in a.position.rejectedStudents
}
check ApplicationsRejectedMatchPositionsOutcome for 5

assert InternshipsMatchApplications {
  all i: Internship |
    all sel: i.selection |
      some a: Application |
        a.student = i.student
        and a.position = sel.position
        and a.student = sel.student
}
check InternshipsMatchApplications for 5

assert UniqueOngoingInternships {
  all s: Student |
    no disj i1, i2: s.internships |
      i1.status = Ongoing and i2.status = Ongoing
}
check UniqueOngoingInternships for 5


--PRED

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

--Second world: 2 students, 1 company, 1 position. Both students apply, one through recommendation. They are both accepted for the selection process, but only one obtains the internship.
pred SecondWorld {
	#Company =1
	#Student= 2
	#Position = 1
	#Application =2
	#Selection =2
	#Recommendation=1
	#Internship=1
}

run SecondWorld for 4
















