# Compiled and published paper artifacts

Scope: checked-in PDFs, review builds, release artifacts and their provenance. These are delivery artifacts, not interchangeable copies of a TeX filename.

### paper-01
Each paper artifact has an unambiguous identity: document, version or revision, content hash, date, provenance, and status as a review build, author-supplied publication, or historical edition. A published artifact additionally identifies its actual publication record/DOI when one exists.

Check: artifact and provenance record. Distinct companion manuscripts are not treated as versions of the same document.

### paper-02
A PDF claimed to represent repository source is traceable to the exact source/input identities and build environment that produced it. An imported published PDF whose exact source/build provenance is unavailable says so, instead of implying reproducibility or a source match that has not been established.

Check: source-to-output manifest or explicit unknown provenance. Byte-identical reproducibility is not assumed when timestamps or nondeterministic PDF metadata vary; content identity and any normalization method remain explicit.

### paper-03
Source may advance ahead of the published PDF. A source correction is not reported as published until the intended published artifact is verified to contain it. When the designated current source and designated published PDF differ, the relationship and any advertised currency are truthful. If synchronizing them is an accepted publication goal, the remaining obligation has a visible canonical record; exploratory newer TeX does not by itself create a publication commitment, and an old PDF may remain valid historical evidence.

Check: actual artifact content, version/hash, source comparison and publication-stage acceptance. “Stale” is relative to a claimed source/edition, not merely file age.

### paper-04
An artifact accepted for reading has legible equations and figures, functioning meaningful references, and no newly introduced clipping, missing glyphs, blank/missing pages or misdirected links in the affected content. Review evidence includes targeted rendered inspection as well as logs or extracted text.

Check: affected-page inspection and source/base comparison. Existing layout warnings are classified by reader impact rather than automatically treated as new blockers.
