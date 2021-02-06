
(defun is-variable? (term)
	(if (stringp term) (upper-case-p (char term  0)) nil)
)

(defun resolve-facts (query facts) 
    (print facts)
	(let ((first (car facts)))
		(if (not first) nil
			(if (resolve-fact query first) (resolve-fact query first)
				(if (not (cdr facts)) nil (resolve-facts query (cdr facts)))))
	)
)

(defun resolve-fact (query fact) 
	(let ((data (list fact))
		(mapping (assign-params query query)))
		(if (if (same-predicate query fact) (init-params query fact) nil)
			(let ((update-result (update-result (second query) (if (same-predicate query fact) (init-params query fact) nil)))) 

				(solution mapping update-result)) 
				nil)
		
	)
)
;; Based on the list of rule which matches the query, resolve them one by one
(defun solve (matched-rules query facts rules)
	(let ((first (car matched-rules)))
		(if (not first) (resolve-facts query facts) 
			(if (resolve-single first query facts rules) (resolve-single first query facts rules)
				(if (not (cdr matched-rules)) nil (resolve (cdr matched-rules) query facts rules))))
	)
)

;; Based on the list of rule which matches the query, resolve them one by one
(defun resolve (matched-rules query facts rules)
	(let ((first (car matched-rules)))
		(if (not first) '() 
			(if (resolve-single first query facts rules) (resolve-single first query facts rules)
				(if (not (cdr matched-rules)) nil (resolve (cdr matched-rules) query facts rules))))
	)
)
;; Select a rule and resolve it, if it's satisfied (return a list of values), stop program and show the result,
;; Otherwise, continue with the rest rules
(defun resolve-single (matched-rule query facts rules)
	(let ((data (second matched-rule))
		(predicate (first matched-rule))
		(mapping (assign-params query (first matched-rule))))

		(if (if (not mapping) nil (match data query facts rules))
			(let ((update-result (update-result (second (first matched-rule)) (if (not mapping) nil (match data query facts rules))))) 

				(solution mapping update-result)) 
				nil)
		
	)
)

;; This is a function which map the unification with the variable from the query 
(defun solution (mapping result)
	(if (not mapping) '()	
		(append (check-solution (car mapping) result) (solution (cdr mapping) result)))

)

;; Example mapping = ("X" "Y") and the result is ("Y" "horse"), this will replace value of Y to X
(defun check-solution (mapping result)
	(list (cons (first mapping)(scan-result (second mapping ) result)))
)
;; Hepler function for check-solution
(defun scan-result (value result)
	(if (not (is-variable? value)) (list value) 
		(if (not result) '()	
			(if (equal value (first (first result))) (list (second (first result)))
			(scan-result value (cdr result)))))
)

;; Just remove some duplicated values from list
(defun update-result (params mapping)
    
	(if (not mapping) '() 
		(append (update-result params (cdr mapping)) (check params (car mapping))))
)

;; Check if it's duplicated
(defun check (params value)
	(if (member-list (first value) params) (list value) '() )
)

;; reolve the list of predicate from hand side of the rules
(defun match (matched-rule query facts rules)
	(let ((x (first matched-rule)))
		(if (cdr matched-rule) 
			(if (and (test x facts) (match (cdr matched-rule) query facts rules))
				(append-list (test x facts) (match (cdr matched-rule) query facts rules))
				(resolve (get-matched-rules x rules) x facts rules)) 
					(if (test x facts) (test x facts) (resolve (get-matched-rules x rules) x facts rules)))
	)
)

;; initialize the variables
(defun init-params (x1 x2)
	(let ((p1 (second x1)) (p2 (second x2)))
		(if (can-assign p1 p2) (assign p1 p2) '())
	)
)
;; hepler function for mapping params between quert and left hand side of the rule
(defun assign-params (x1 x2)
   (let ((p1 (second x1)) (p2 (second x2)))
		(force-assign p1 p2)
	)
)
;; force assign value regardless variable of not
(defun force-assign (x1 x2)
	(let ((p1 (first x1)) (p2 (first x2)))
		(let ((assignment (if (or (not p1) (not p2)) nil (if (or (is-variable? p1) (is-variable? p2))(list p1 p2) (if (equal p1 p2) (list p1 p2) nil )))))		
			(if (and (not (first x1)) (not (first x2))) '() 
				(if (not assignment) (assign (cdr x1) (cdr x2)) (cons assignment (assign (cdr x1) (cdr x2))))))
	)
)
;; assign value of variable
(defun assign (x1 x2)
	(let ((p1 (first x1)) (p2 (first x2)))
		(let((assignment (if (or (not p1) (not p2)) nil 
					(if (is-variable? p1) (list p1 p2) (if (equal p1 p2) (list p1 p2) nil)))))		
			(if (and (not (first x1)) (not (first x2))) '() 
				(if (not assignment) (assign (cdr x1) (cdr x2)) (cons assignment (assign (cdr x1) (cdr x2))))))
	)
)
;; Check if can assign value for variable
(defun can-assign (x1 x2)
	(let ((p1 (first x1)) (p2 (first x2)))
		(if (and (not p1) (not p2)) t 
			(if (not (if (or (not p1) (not p2)) nil 
					(if (is-variable? p1) t 
						(if (equal p1 p2) t nil)))) nil (can-assign (cdr x1) (cdr x2))))
	)
)
;; Resolve each predicate at right hand side of the rule
;; Example (("legs" ("X" 2)) (("mammal" ("X")) ("arms" ("X" 2)))), try to resolve mammal and arms
(defun test (x facts)
	(let ((first (first facts)))
		(if (not first) '() 
			(if (and (same-predicate x first) (init-params x first)) (append (init-params x first) (test x (cdr facts))) 
				(test x (cdr facts))))
		
	)
)

;; Main program 
(defun run (program)

	;; Get a list of query, facts and rules 
	(let ((query (get-query program))
		 (facts (get-facts program))
		 (rules (get-rules program))
		 )
		(let ((result (solve (get-matched-rules query rules) query facts rules)))
		
			;; If the list of values less than the required params in query, fail
			;; If they're equal, just keep the variable (remove the constant)
			;; If all prams in query is constant, return true ( because empty list is for failure)
			(if (< (length result ) (length (second query))) (list "False")
				(let ((data (show-result (print result))))
					(cond
						(data data) 
						((check-true-or-false result) (list "True"))  
						(T (list "False"))
				))
			)
		)
	)
)

;; Show result as above logic
(defun show-result (result)
	(if (not result) '()
		(let ((first (first result)))
			(if (is-variable? (first first)) (cons first (show-result (cdr result))) 
				(if (equal (first first) (second first))(show-result (cdr result)) nil))
			))
)



(defun read-file (filename) 
	(read-from-string (reduce (lambda (a b) (concatenate 'string a b)) 
		(with-open-file (stream filename)
		    (loop for line = (read-line stream nil)
		          while line
		          collect line)))))


(defun write-to-file (output-data filename)
	(with-open-file (stream filename :direction :output) 
		(format stream "~{~a~^~%~}" output-data)))
	

(defun main ()
	(let ((output-data (run (read-file "input.txt"))))
		(write-to-file output-data "output.txt")))
	


;; Check if should return true (T) or empty list 
(defun check-true-or-false (result)
	(if (not result) t

		(let ((first (first (first result))) (second (second (first result))))
			(if (and (not (is-variable? first)) (not (equal first second))) nil (check-true-or-false (cdr result)))
			))
)

;; Get query from parsed clauses
(defun get-query (program)
	(let ((first (car program)))
		(if (car first) (get-query (cdr program)) (second first))
	)
)

;; Get facts from parsed clauses
(defun get-facts (program)
	(let ((first (car program)))
		(if (not first) '() 
			(if (nth 1 first) (get-facts (cdr program)) (cons (car first) (get-facts (cdr program))) ))
	)
)

;; Get rules from parsed clauses

(defun get-rules (program)
	(let ((first (car program)))
		(if (not first) '() 
			(if (not (nth 0 first)) (get-rules (cdr program)) 
				(if (not (nth 1 first)) (get-rules (cdr program)) 
					(cons first (get-rules (cdr program))))))
	)
)

;; Get rule match the query 
(defun get-matched-rules (query rules)
	(let ((first (car rules)))
		(if (not first) '() 
			(if (same-predicate (nth 0 first) query) (cons first (get-matched-rules query (cdr rules)))
				(get-matched-rules query (cdr rules))))
				
	)
)

;; Check the same predicate or not
(defun same-predicate (query1 query2)
	(let ((f1 (first query1)) (f2 (first query2)))
		(if (string-equal f1 f2) f1 nil)
	)
)

;; List helper functions
(defun append-member (E L)
     (if (member-list E L) L (append E L))
)
(defun append-list (L1 L2)
	(if (not L1) L2
		(append-member (car L1)(append-list (cdr L1) L2)))
)

(defun member-list (E L)
     (if (not L) nil
		(if (not (equal E (car L))) (member-list E (cdr L)) t))
)

(main)