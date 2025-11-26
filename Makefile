# Makefile for TCP-AAD Formal Verification
# Automates Spin model checking workflow

.PHONY: all verify clean help safety trace paper

# Default target
all: verify

# Compile and run basic verification
verify: tcp_aad.pml
	@echo "=== Compiling Promela model ==="
	spin -a tcp_aad.pml
	@echo "\n=== Compiling verifier ==="
	gcc -o pan pan.c
	@echo "\n=== Running verification ==="
	./pan -m100000
	@echo "\n=== Verification complete ==="

# Run with assertion checking only (ignore invalid end states)
safety: tcp_aad.pml
	@echo "=== Compiling Promela model ==="
	spin -a tcp_aad.pml
	@echo "\n=== Compiling verifier (no reduction) ==="
	gcc -DNOREDUCE -o pan pan.c
	@echo "\n=== Running safety property verification ==="
	./pan -A -m100000
	@echo "\n=== Safety verification complete ==="

# Generate and replay error trace
trace: pan.trail
	@echo "=== Replaying error trace ==="
	spin -t -p tcp_aad.pml

# Run simulation (random execution)
simulate: tcp_aad.pml
	@echo "=== Running random simulation ==="
	spin -p tcp_aad.pml

# Verbose verification with statistics
verbose: tcp_aad.pml
	@echo "=== Compiling Promela model ==="
	spin -a tcp_aad.pml
	@echo "\n=== Compiling verifier ==="
	gcc -o pan pan.c
	@echo "\n=== Running verification (verbose) ==="
	./pan -m100000 -v
	@echo "\n=== Verification complete ==="

# Verify specific LTL property
# Usage: make ltl PROP=property_name
ltl: tcp_aad.pml
	@if [ -z "$(PROP)" ]; then \
		echo "Error: Please specify property name"; \
		echo "Usage: make ltl PROP=delayed_segments_bounded"; \
		exit 1; \
	fi
	@echo "=== Verifying LTL property: $(PROP) ==="
	spin -a -N $(PROP) tcp_aad.pml
	gcc -o pan pan.c
	./pan -a
	@echo "\n=== LTL verification complete ==="

# Compile paper
paper:
	@echo "=== Compiling paper ==="
	cd paper && pdflatex main.tex
	cd paper && bibtex main
	cd paper && pdflatex main.tex
	cd paper && pdflatex main.tex
	@echo "\n=== Paper compiled: paper/main.pdf ==="

# Clean generated files
clean:
	@echo "=== Cleaning generated files ==="
	rm -f pan pan.* *.trail _spin_nvr.tmp
	rm -f paper/*.aux paper/*.bbl paper/*.blg paper/*.log paper/*.out
	@echo "=== Clean complete ==="

# Show help
help:
	@echo "TCP-AAD Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make verify   - Compile model and run verification"
	@echo "  make safety   - Run safety property verification only"
	@echo "  make trace    - Replay error trace (if violations found)"
	@echo "  make simulate - Run random simulation"
	@echo "  make verbose  - Run verification with detailed output"
	@echo "  make ltl      - Verify specific LTL property"
	@echo "                  Usage: make ltl PROP=property_name"
	@echo "  make paper    - Compile LaTeX paper to PDF"
	@echo "  make clean    - Remove all generated files"
	@echo "  make help     - Show this help message"
	@echo ""
	@echo "Example workflow:"
	@echo "  1. make verify    # Run basic verification"
	@echo "  2. make safety    # Check safety properties"
	@echo "  3. make trace     # If errors found, replay trace"
	@echo "  4. make paper     # Compile documentation"
