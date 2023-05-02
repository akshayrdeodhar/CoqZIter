report.pdf: report.md references.bib
	 pandoc --number-sections --citeproc -o report.pdf report.md

clean:
	rm report.pdf
