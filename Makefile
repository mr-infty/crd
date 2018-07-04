.phony: compute-A compute-B compute-C compute-D compute-F compute-E compute-G compute-all

SAGE = /Applications/SageMath/sage

A_RANGE = 1 2 3 4 5 6 7 8
B_RANGE = 2 3 4 5 6 7 8
C_RANGE = 2 3 4 5 6 7 8
D_RANGE = 3 4 5 6 7 8
E_RANGE = 6 7 8
F_RANGE = 4
G_RANGE = 2

compute: compute-A compute-B compute-C compute-D compute-E compute-F compute-G

compute-A:
	@echo "Computing cohomology of type A"
	$(SAGE) main.py A $(A_RANGE)

compute-B:
	@echo "Computing cohomology of type B"
	$(SAGE) main.py B $(B_RANGE)

compute-C:
	@echo "Computing cohomology of type C"
	$(SAGE) main.py C $(C_RANGE)

compute-D:
	@echo "Computing cohomology of type D"
	$(SAGE) main.py D $(D_RANGE)

compute-E:
	@echo "Computing cohomology of type E"
	$(SAGE) main.py E $(E_RANGE)

compute-F:
	@echo "Computing cohomology of type F"
	$(SAGE) main.py F $(F_RANGE)

compute-G:
	@echo "Computing cohomology of type G"
	$(SAGE) main.py G $(G_RANGE)
