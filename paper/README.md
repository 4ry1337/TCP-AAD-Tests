# TCP-AAD Formal Verification Paper

This directory contains the LaTeX source for the academic paper on formal verification of TCP-AAD.

## Paper Structure

**Title**: Formal Verification of TCP-AAD: Adaptive Delayed Acknowledgment over Wi-Fi Using SPIN Model Checker

**Format**: IEEE Conference format

## Files

- `main.tex` - Main paper file (includes all sections)
- `references.bib` - Bibliography with 25+ references
- `sections/` - Individual paper sections:
  - `introduction.tex` - Introduction and motivation
  - `background.tex` - TCP DACK, Wi-Fi aggregation, formal verification background
  - `related_work.tex` - Survey of related verification work
  - `methodology.tex` - SPIN, time abstraction, verification workflow
  - `formal_models.tex` - Promela models description (Basic, DACK, AAD)
  - `properties.tex` - LTL property specifications
  - `results.tex` - Verification results and statistics
  - `discussion.tex` - Interpretation, limitations, future work
  - `conclusion.tex` - Summary and closing remarks

## Compilation

### Requirements

- LaTeX distribution (TeX Live, MiKTeX, or MacTeX)
- BibTeX for bibliography
- Required packages: cite, amsmath, algorithmic, graphicx, listings, hyperref, booktabs

### Compile Commands

```bash
cd paper

# Full compilation with bibliography
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex

# Or use latexmk for automatic compilation
latexmk -pdf main.tex
```

### Quick Compile (no bibliography update)

```bash
pdflatex main.tex
```

## Output

- `main.pdf` - Final paper PDF

## Paper Statistics

- **Sections**: 9 (Introduction through Conclusion)
- **Pages**: Approximately 12-15 pages in IEEE two-column format
- **References**: 30+ citations
- **Figures/Tables**: 10+ tables with verification results
- **Code Listings**: Promela examples with syntax highlighting

## Content Summary

### Abstract

Presents first formal verification of TCP-AAD using SPIN, exploring 67-75M states with 100% pass rate (9/9 properties).

### Key Contributions

1. Three Promela models (Basic TCP, DACK, TCP-AAD)
2. Nine verified temporal logic properties
3. Comprehensive state space analysis (67-75 million states)
4. Demonstration that AAD generates 36% fewer transitions than DACK

### Key Results

- ✅ All 9 properties verified (100% pass rate)
- ✅ Zero bugs found
- ✅ RFC 1122 compliance proven
- ✅ Adaptive behavior validated
- ⏱️ Verification time: 9 minutes

## Citation

```bibtex
@inproceedings{tcpaad_verification2025,
  title={Formal Verification of TCP-AAD: Adaptive Delayed Acknowledgment over Wi-Fi Using SPIN Model Checker},
  author={[Your Name]},
  booktitle={[Conference Name]},
  year={2025},
  organization={Innopolis University}
}
```

## Related Files

- `../models/` - Promela source models
- `../scripts/` - Verification automation scripts
- `../docs/VERIFICATION_REPORT.md` - Detailed technical report
- `../SUMMARY.md` - Quick results summary

## Notes for Instructors

This paper is suitable for:
- Formal Methods courses
- Software Engineering courses with verification focus
- Network Protocols courses with correctness emphasis
- Graduate seminars on model checking

**Learning Objectives Demonstrated**:
1. Model checking with SPIN
2. LTL property specification
3. Time abstraction in untimed model checkers
4. Real-world protocol verification
5. State space analysis and optimization

## Customization

To customize for your submission:

1. Update author information in `main.tex` (line 51-56)
2. Adjust abstract if needed (keep under 200 words)
3. Add acknowledgments section if required
4. Include your affiliation and email

## LaTeX Tips

### View Compilation Errors

```bash
grep -i error main.log
```

### Clean Build Artifacts

```bash
rm -f *.aux *.bbl *.blg *.log *.out *.toc
```

### Convert to Other Formats

For arXiv submission:
```bash
# Ensure all .tex files use relative paths
# Package all sources
tar czf paper.tar.gz main.tex sections/ references.bib
```

## Support

For LaTeX issues:
- Check `main.log` for error details
- Ensure all packages are installed
- Try `pdflatex -interaction=nonstopmode main.tex` for batch processing

For content questions:
- Refer to `../docs/VERIFICATION_REPORT.md` for technical details
- See `../SUMMARY.md` for high-level overview
- Check verification results in `../results/verification_outputs/`

---

**Status**: ✅ Complete and ready for submission

**Last Updated**: November 9, 2025
