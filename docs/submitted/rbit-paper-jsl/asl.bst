% File asl.bst, version 1.0, March 1, 2000.
% Christos A. Kapoutsis, ckap@math.uoa.gr.
% Copyright 2000 by the Association for Symbolic Logic.
%
% This file carries the usual TEX-file non-warranty for results and
% it can be freely copied and re-distributed provided that IF IT IS
% CHANGED IN THE SLIGHTEST WAY, it must be RENAMED.








%%%====================================================================
%%%=-1== Important notes for the user =================================
%%%====================================================================



% COMMANDS THAT THE TEX USER SHOULD DEFINE
%
% Any LaTeX file that uses this BibTeX style, must have the following
% commands defined:
%    1. The command \bysame, as in (++).
%    2. The command \weaktie, as in (+).
%    3. The \biband, \bibetal commands.
%    4. The \jslname, \bslname commands, see (ynm).
%    5. The \yearmagic command, as in (@). See also (@@), for a
%       relevant suggestion.
%    6. The \guysmagic command, as in (&). See also (&&).
%    7. The \guy command, to comply with syntax (**).
%    8. The \TheSortKeyIs command, as in (*).
%    9. The \bibfitem, \bibritem commands, to comply with syntax (!).
% See file asl.cls for examples of such definitions. (Or aslbstx.sty.)


% ASSUMPTIONS
%
% The following two assumptions are made:
%
% 1. No entry is such that the list of author names is immediately
%    followed by the year of publication.
% 2. No entry is such that the list of author names is its last
%    block.
%
% It is most probable that both these rules hold, since there should
% always be a title, which is positioned right after the name list.
% If they fail, then the \guysmagic & \yearmagic tricks may not work
% properly.








%%%====================================================================
%%%==0== General description ==========================================
%%%====================================================================


% THE BIBLIOGRAPHY STORY
% Read this section for a description of how a bibliography listing is
% created by LaTeX and BibTeX.
%
% Suppose I am preparing a paper in TeX, say `paper.tex', and I want a
% bibliography to be inserted into it. I do four things:
%    1. Prepare one or more bibliography databases, in the special
%       format required by BibTeX (see [1],[3]). The names of the
%       files that contain these databases should have the extension
%       `bib'. Let them be `data1.bib', ..., `dataN.bib'.
%    2. Prepare one bibliography style file, in the special language
%       recognized by BibTeX (see [2]). The name of that file should
%       have the extension `bst'. Let it be `style.bst'. File `asl.bst'
%       is such a file.
%    3. In `paper.tex', insert the command
%          \bibliography{data1,..,dataN}
%       at the point where the bibliography should appear, and also
%       the command
%          \bibliographystyle{style}
%       anywhere before that.
%    4. In `paper.tex', insert the command
%          \cite{name}
%       each time I want to refer to an entry of the bibliography named
%       `name'. I should also insert the command
%          \nocite{name}
%       if I want the entry named `name' to appear in the bibliography
%       listing, ot the command
%          \nocite{*}
%       if I want all bibliography entries to appear in the listing.
%
% Then I type
%         latex paper                                (LaTeX first pass)
% and LaTeX reads `paper.tex'. Processing this file, it creates a new
% file named `paper.aux'. In `paper.tex', a command of the form of the
% left column below causes the corresponding command in the right
% column to be printed into `paper.aux'.
%         \bibliography{data1,..,dataN}   \bibdata{data1,..,dataN}
%         \bibliographystyle{style}       \bibstyle{style}
%         \cite{name}                     \citation{name}           (#)
%         \nocite{name}                   \citation{name}
%         \nocite{*}                      \citation{*}
% This way, after the processing is over, `paper.aux' contains:
%    A. The list of the names of all bibliography database files that
%       I intend to use (parameters to the \bibdata command). That is,
%       `data1.bib',..,`dataN.bib'.
%    B. The name of bibliography style that I intend to use (parameter
%       to the \bibstyle command). That is, `style.bst'.
%    C. The names of the bibliography entries that I want to appear
%       in the bibliography listing (parameters to the several
%       \citation commands). Let them be `name1',..,`nameN'.
%    D. \citation{*} iff I want all the entries of the bibliography
%       databases to appear in the bibliography listing.
%
% Then I can type
%         bibtex file
% and BibTeX will read `paper.aux', looking for the (#) commands and
% ignoring all other contents of the file. At the end, it has got all
% of the (A), (B), (C), (D) information. So, it executes `style.bst'
% over each one of `data1.bib',..,`dataN.bib', extracting from them
% the entries named `name1',...,`nameN' (or all entries, in case of
% \citation{*}) and printing them into a new file, named `paper.bbl',
% in a special TeX format (a `thebibliography' environment, which is
% just a special `list' environment).
%
% Then I can type
%         latex paper                               (LaTeX second pass)
% and LaTeX first reads `paper.aux', ignoring each of the (#) commands
% (each one of these commands has a "gobbling" definition); the sole
% purpose of these commands is to pass information to BibTeX, not to
% LaTeX. In the sequel, LaTeX reads `paper.tex'. When it reaches the
%         \bibliography{data1,..,dataN}
% command, it \input's `paper.bbl' (the file created by BibTeX, a
% `thebibliography' environment) which causes the bibliography listing
% to appear in the `paper.dvi' file.
%   [  This \input is actually a command of the form
%      	\IfFileExists{paper.bbl}
%            {\input paper.bbl}
%            {\typeout{No file paper.bbl.}}
%      and is also executed -with trival effects- during the first
%      run of LaTeX.  ]
% However, the content of `thebibliography' environment is not a simple
% list of \item's. It is actually a list of \bibitem's. And each one of
% them not only expands to an \item (thus making the list of \bibitem's
% something _more than_ a list of \item's), but also outputs a
%         \bibcite{name}{label}
% command to `paper.aux'. This information is intended to pass to the
% next (third) LaTeX run and its meaning is that "the entry named
% `name' should have citation label `label'".
%
% Then I can type
%         latex paper                                (LaTeX third pass)
% and LaTeX first reads again `paper.aux'. Each time a command
%         \bibcite{name}{label}
% is read, the TeX control sequence `b@name' is defined to expand to
% `label'. Then, knowinf this new definition, LaTeX reads `paper.tex'.
% And, when the \cite{name} command appears, the `b@name' macro is
% expanded, to give `label' in place.
%
% In short, the whole process consists of the following steps:
%    i. First pass of LaTeX.
%          Reads .tex.
%          Creates .aux, outputing there all information
%             needed by BibTeX: \bibstyle,\bibdata,\citation.
%   ii. Pass of BibTeX.
%          Reads .aux.
%          Creates .bbl = a `thebibliography' environment
%                       = a list of \bibitem's.
%  iii. Second pass of LaTeX.
%          Reads .aux, ignoring information intended for BibTeX.
%          Then reads .tex, inputs .bbl at \bibliography.
%          Creates .aux as in first pass; but also: Each \bibitem
%             command outputs a \bibcite to .aux.
%   iv. Third pass of LaTeX.
%          Reads .aux, ignoring iformation intended for BibTeX,
%             defining all \b@name macros out of \bibcite's.
%          Then reads .tex, replaces \cite{name} with the expansion
%             of \b@name, inputs .bbl at bibliography.
%          Creates .aux as in second pass.


% WHAT A BIBLIOGRAPHY STYLE FILE (.bst file) DOES
% Read this section for a description of what a bibliography style
% file does (and also what asl.bst does).
%
% A bibliography style file (.bst file) is a program, written in
% BibTeX's special language (see [2],[4]), that describes how the
% bibliography database files (.bib files) that one includes in the
% `\bibliography' LaTeX command are to be processed.
%
% A style doesn't describe everything in how the databases are to be
% read; some things are fixed: in each database BibTeX expects to find
% a sequence of structures of the form (a spaces implies any nonempty
% sequence of blank characters: spaces, carriage returns, tabs etc.):
%      @ENTRYTYPE {name, field1 = "value1", ..., fieldN = "valueN" }
% and ignores everything that is not contained in such a structure.
% Naturally, each such structure is intended to describe one entry of
% the database.
%
% Upon this fixed supposition, a style defines the following:
%   (A) What entry types there are. The standard styles,
%       allow the following 14 entry types:
%          article, book, booklet, conference, inbook,
%          incollection, inproceedings, manual, masterthesis,
%          misc, phdthesis, proceedings, techreport, unpublished.
%       The same goes for asl.bst, too.
%   (B) What fields may be defined within each entry (any entry
%       of an allowed type). The standard styles, allow the following
%       24 fields:
%          address, annote, author, booktitle, chapter, crossref,
% 	   edition, editor, howpublished, institution, journal,
%          key, month, note, number, organization, pages,
%          publisher, school, series, title, type, volume, year.
%       In addition to these, asl.bst also allows the following:
%          language, hardcite, hardlist, hardsort, hardxtra.
%       The first one is just one more attribute of the publication
%       that the entry describes. The `hard' ones enhance the
%       flexibility of the user in formatting that entry in LaTeX.
%   (C) How each one of the finally selected entries will be
%       formatted in TeX.
% This special behavior of a style is determined in the following ways:
%   (B) is specified by the ENTRY command. For asl.bst, see Section 1B.
%   (C) is specified by defining a function whose name is the same with
%       the name of the corresponding entry type. For example, to
%       specify how the `article' entry type should be handled, one
%       just defines a
%       	 FUNCTION {article} { ... }
%       that contains all actions to be performed for the processing of
%       an entry of this type. (The function can access the value of
%       any field of the entry, through the actual name of that field.)
%       For asl.bst, see Section 4B.
%   (A) is specified implicitly: An entry of type X that appears in the
%       database is accepted by the style only if the style contains a
%          FUNCTION {X} {...}
%       which, by (C), also determines how this entry is formatted.
%       (This way, more than the desired entry types are `accepted'.
%       For example, asl.bst also accepts an entry of the type `not',
%       because there is a function named this way. However, these extra
%       entry types trigger only erroneous actions, most probably.)


% THE STUCTURE OF asl.bst
%
% The first task is the declarations: of the entry types (as explained
% by (A)), of the definable fields (as explained in (B)), of all
% variables used in the program (see [2]), and of the macros for month
% abbreviations (see [3]). These are all done in Section 1, Subsections
% 1A, 1B, 1C, and 1D, respectively.
%
% The second task is reading the databases. This is done in Section 5
% (the easiest section, just one command). BibTeX reads all specified
% (via the \bibdata command) databases and constructs the list L of
% all selected (via \citation commands) entries.
%
% The third task is sorting list L. This is done in Section 6.
%
% The fourth task is calculating some extra fields for each entry.
% This is done in Section 7. The extra fields are the following:
%    a. same.flag   In Subsection 7B. This is either 1 or 0, depending
%                   on whether the entry follows another entry with the
%                   same author(s) or not.
%    b. xtra.label  In Subsection 7C. This is "a","b",... , when the
%                   entry belongs to a sublist of successive entries
%                   with the same author(s) & year. Otherwise, it is
%                   "".
%    c. name.label  In Subsection 7D. This is a list of one or more
%                   \guy commands, that contains proper punctuation &
%                   conjunctors and fully describes the author(s) of
%                   the entry. See below for what a \guy command does.
% The calculation of each field is done separately and requires one
% or two iterations over list L. It is possible to implement these
% calculations altogether, with only two iterations. Nevertheless,
% such an implementation would be too complicated and only a little
% faster.
%
% The last task is the creation of the .bbl file. This is done in
% Subsection 8.
%
% Section 2 contains several functions of general purpose.
% Section 3 contains the functions that are responsible for the
%           output to the .bbl file.
% Section 4 contains all functions that implement the formatting
%           of the entry fields (Subsection 4B) and then of the
%           entries themselves (Subsection 4C).
% The main reason why these three sections do not come right before
% Section 8 is that all functions of Section 4 must have been declared
% when the READ command of Section 5 is executed. Otherwise, in
% accordance with (A), BibTeX wouldn't know what types of entries are
% acceptable.


% YEAR MAGIC
% Read this section, if you wonder what the \yearmagic command does.
%
% To make the style flexible, we have to allow that the year of an
% entry may appear at its beginning, like:
%       Kapoutsis [2020] $\P=\NP$, Kapoutsis \& co, Koufalia.
% This implies that two tasks should be performed:
%       1. Printing the year at the beginning.
%       2. Not printing the year at its normal position, somewhere
%          inside the entry.
% The first task can be accomplished through a proper definition of
% the \bib?item commands. This section discusses the trick that
% performs the second task.
%
% The first thought was the following: (i) We change the style so
% that, whenever year-relevant-stuff is to be printed, the string
%	\yearmagic{year-relevant-stuff}
% is output instead of the intended string
%       year-relevant-stuff
% and (ii) we define the command \yearmagic as
%       \def\yearmagic#1{#1}      or     \def\yearmagic#1{}
% depending on whether we want the year to appear or disappear.
%
% This is fine, except for a problem with punctuation: If the
% year-relevant-stuff appears in an entry like that:
% A.        ...Springer-Verlag, \yearmagic{2020}, pp. 20--21,...
% forcing it to disappear will lead to
% A'.       ...Springer-Verlag, , pp. 20,...
% which is not what we wanted. Analogously, in the context
% B.        ...Springer-Verlag, \yearmagic{1999}.
% the year's disappearence will give
% B'.        ...Springer-Verlag, .
% On the contrary, everything is okay in contexts like
% C.        ...Springer-Verlag, May\yearmagic{1999}, pp. 20,...
% D.        ...Springer-Verlag, May\yearmagic{1999}.
% (that is, when something precedes the year-relevant-stuff in the
% same block), so long as we take care that the \yearmagic will be
% printed immediately after (no spaces) the preceding material and
% that its expansion, if nonempty, will start with a space.
%
% To beat this punctuation problem we change the \yearmagic command
% a bit. We give it one more argument (made first) which is intended
% to be either empty ("") or comma (","). Then, we correct the .bbl
% output so that cases A, B, C, D are printed like that:
% A*.       ...Springer-Verlag\yearmagic{,}{1999}, pp. 20,...
% B*.       ...Springer-Verlag\yearmagic{,}{1999}.
% C*.       ...Springer-Verlag, May\yearmagic{}{1999}, pp. 20,...
% D*.       ...Springer-Verlag, May\yearmagic{}{1999}.
% and we define \yearmagic as follows
% (@)     \def\yearmagic#1#2{#1 #2}   or   \def\yearmagic#1#2{}
% depending on whether we want the year to appear or disappear. You
% can check that everything is okay now.
%
% Correcting the way A, B, C, D are printed is done:
%    1. in functions format.vol.year and format.date (the only
%       functions that format strings with year-relevant-stuff).
%       There it is obvious whether additional material is going to
%       precede the year-relevant-stuff, so it is easy to decide
%       what the first argument of the \yearmagic command should be.
%    2. in function output.nonnull. There, we check whether the
%       block that is currently printed [the (i-1)'th block, in the
%       terminology of that function's comments] will be followed by
%       a block that contains the \yearmagic command with no preceding
%       material. If so, no comma is inserted between the two blocks,
%       exactly because the expansion of the \yearmagic command will
%       provide this comma (if necessary). Otherwise, the comma is
%       normally inserted.
%
% Remember that the style file should define the \yearmagic command
% as in (@). Suggestion: A couple of commands like the following
% (@@)    \def\yearappear{\def\yearmagic##1##2{##1 ##2}}
%         \def\yeardisappear{\def\yearmagic##1##2{}}
% will make the (dis)appearence of the year as easy as a declaration
%     \yearappear            or            \yeardisappear
% anywhere before the bibliography.
%
% A complicated trick, for a complicated need.


% GUYS MAGIC
% Read this section, if you wonder what the \guysmagic command does.
%
% Apart from the year-relevant-stuff, the list of names (authors or
% editors) in an entry may also have to disappear. To this end:
%  1. The format.authors and format.editors functions were altered so
%     that they enclose their return strings in a \guysmagic command.
%  2. The output.nonnull function is altered so that it does not
%     append a comma to a \guysmagic block.
%  3. The \guysmagic macro must be defined, as follows
%     (&)      \def\guysmagic#1{#1,}       or      \guysmagic#1{}
%     depending on whether we want the names to appear or not.
%     As in `year magic', it is also possible to define
%     (&&)     \def\guysappear{\def\guysmagic##1{##1,}}
%              \def\guysdisappear{\def\guysmagic##1{}}
%     so that (dis)appearence of the names is a matter of simple
%     declaration:
%              \guysappear       or       \guysdisappear.


% REFERENCES
%
% [1] `BibTeXing'. Oren Patashnik, 8 February 1988.
% [2] `Designing BibTeX styles'. Oren Patashnik, 8 February 1988.
% [3] Appendix B of `LaTeX: A document preparation system'.
%     Leslie Lamport, Addison-Wesley, 1986.
% [4] File btxbst.doc.








%%%====================================================================
%%%==1== Declarations =================================================
%%%====================================================================



%%%==1A. Entry types ==================================================
% According to [1], standard BibTeX style files should accept the
% following 14 different entry types:
% 	article, book, booklet, conference, inbook, incollection,
%	inproceedings, manual, masterthesis, misc, phdthesis,
%	proceedings, techreport, and unpublished.
% According to [2], there should also be a default entry type, named
%       default.type,
% to handle all other cases. Each of these types is declared merely
% through the presence of a function of the same name, that handles
% the corresponding entries. All these functions can be found below,
% in Section 4C, immediately before the READ command.



%%%==1B. Entry fields =================================================
% According to [1], each entry (of any type) may contain any of the
% following 24 fields:
%       address, annote, author, booktitle, chapter, crossref, edition,
%       editor, howpublished, institution, journal, key, month, note,
%       number, organization, pages, publisher, school, series, title,
%       type, volume, year.
% Here, we also allow the following 5 new fields
%       language, hardsort, hardxtra, hardcite, hardlist
% The first one is just one more attribute of the publication that the
% entry describes. The `hard' ones are explained below.
ENTRY
{ address
  author
  booktitle
  chapter
  edition
  editor
  howpublished
  institution
  journal
  key
  language
  month
  note
  number
  organization
  pages
  publisher
  school
  series
  title
  type
  volume
  year
  % Sorting of the bibliography is done (Section 6) with respect to
  % the sort.key$ field of the entries. This field is calculated for
  % every entry (in function calc.sort.key) out of the values of the
  % other entry fields and is also output in the .bbl file as the
  % argument of a gobbling command named \TheSortKeyIs. Therefore, by
  % inspecting the .bbl file, one can justify the order of the items.
  %
  % Note that the \TheSortKeyIs command is printed from function
  % fin.entry. And its should merely gobble its argument:
  % (*)      \def\TheSortKeyIs#1{}
  %
  % To change this ordering of an entry, we use the hardsort field:
  % First, we inspect the .bbl file to select the desired new position
  % of the entry. Then, we insert into this entry the hardsort field
  % and set it to any value between the sort.key$ values of the two
  % bibliography items that are adjacent to the desired position. The
  % next run of BibTeX will assign this value to the sort.key$ of the
  % specific entry, causing it to sort right into the desired position.
  hardsort
  %
  % First read the comments on the xtra.label entry variable below.
  %
  % Now suppose that two entries X,Y belong to the same author and were
  % published in the same year. The automatic mechanism of section 7C
  % decides one of them, say X, to have xtra.label "a" and the other
  % one, Y, to have xtra.label "b". What happens if you don't like this
  % assignment, but you would instead prefer it the other way round?
  %
  % We solve this problem as follows: We insert into both entries the
  % hardxtra field and set it to "b" in X, and to "a" in Y. The next
  % run of BibTeX will adopt the desired assignment.
  %
  % (This is done as follows: From 7C, it is clear that extra label
  % "a" is assigned to the first --after sorting-- entry in the list,
  % "b" is assigned to the second, etc. Therefore, to impose the
  % assignment implied by the values of the hardxtra field, we need
  % only force the corresponding ordering. But this we can achieve
  % trivially by inserting these values into the sort.key$ strings,
  % right after the year. This need only one line of code in function
  % calc.sort.key.)
  hardxtra
  % There is always the possibility that the citation label (that is,
  % the label used at the point of citation of the entry in the text)
  % is not what we have in mind. In such a case the hardcite field
  % should be inserted in the entry and set to the exact label that
  % we want to appear at the point of citation.
  %
  % Analogously, the hardlist field can be used to force a particular
  % label to appear next to the entry in the bibliography listing.
  %
  % Both these fields are just passed as arguments to the \bib?item
  % commands, in the output.bibitem function of Section 3.
  hardcite
  hardlist
}
{ % In a sequence of two or more successive bibliography items that
  % belong to the same author(s)/editor(s), all items after the first
  % one should not print the explicit author(s)/editor(s) names. They
  % should print a symbol (usually a long dash) denoting repetition.
  % We suppose that this symbol is produced by the macro \bysame,
  % (++)        \def\bysame{\hrule width2cm}
  % as an example. The same.flag entry variable is intended to be
  %    -- 0, if the entry should explicitly print the
  %       author(s)/editor(s) names.
  %    -- 1, if the entry repeats the author(s)/editor(s)
  %       names of the previous entry.
  % Its value is decided in the iteration of section 7B and used in
  % function format.authors of section 4B.
  same.flag
  % This is a number denoting whether the guys that (may) appear
  % in the entry are editor(s) or not, as follows:
  %    value 0:  no guys in the entry, or the guys are authors.
  %    value 1:  one guy in the entry and this is an editor.
  %    value 2:  more than one guy in the entry, all editors.
  % Note that `nonauthor editors' are not taken into consideration
  % in this calulation. I.e., when the entry has both editors and
  % authors, the nofeditors field will be 0.
  % The field is:
  % a. defined here.
  % b. calculated in Section 7E through a separate iteration over
  %    the list of entries.
  % c. printed as the 5th argument of the corresponding \bib?item
  %    command (in output.bibitem) to the .bbl file.
  nofeditors
}
{ % In a sequence of two or more successive bibliography items that
  % belong to the same author(s)/editor(s), and were published in the
  % same year, tags a,b,c,... should be appended to the years of all
  % items. The xtra.label entry variable is intended to be
  %    -- "", if in this item no tag of this kind has to be appended.
  %    -- "a","b","c",... if the corresponding tag has to be appended.
  % Its value is decided in the iteration of Subsection 7C and output
  % as a \bib?item argument in function output.bibitem of Section 3.
  xtra.label
  % String  name.label.one + ... + name.label.ten  is intended to be
  % a list of the \guy(s) of author(s)/editor(s) of the entry. It is
  % computed by function calc.name.label in 7D and output by function
  % output.bibitem to the .bbl file as a \bib?item argument.
  % There should be only one variable, say name.label, for this string.
  % But there are ten of them, because the string tends to be much
  % longer than entry.max$ (see section 5.3 of [2]).
  name.label.one
  name.label.two
  name.label.three
  name.label.four
  name.label.five
  name.label.six
  name.label.seven
  name.label.eight
  name.label.nine
  name.label.ten
}



%%%==1C. Variables ====================================================
% Scratch variables.
STRINGS  { r s t }

% Scratch variables.
INTEGERS { len i }

% Counters. Used by format functions.
INTEGERS { nameptr namesleft numnames }

% Flag. Is set to true when the construction of a bibitem starts
% (in output.bibitem) and is always false after the first block
% of the bibitem is output (in output.nonnull).
INTEGERS { at.bibitem.start }

% Flag. Use in multi.page.check, in 4A.
INTEGERS { multiresult }

% For sections 7B, 7C.
STRINGS { prev.author curr.author }
% For section 7C.
STRINGS { prev.year curr.year next.xtra }

% Index, for section 7D.
INTEGERS {active.nl.part}



%%%==1D. Month abbreviations ==========================================
% According to [3]'s Section 3, there should be the standard
% abbreviations for the names of months.

MACRO {jan} {"January"}
MACRO {feb} {"February"}
MACRO {mar} {"March"}
MACRO {apr} {"April"}
MACRO {may} {"May"}
MACRO {jun} {"June"}
MACRO {jul} {"July"}
MACRO {aug} {"August"}
MACRO {sep} {"September"}
MACRO {oct} {"October"}
MACRO {nov} {"November"}
MACRO {dec} {"December"}








%%%====================================================================
%%%==2== General purpose functions ====================================
%%%====================================================================



%%%==2A. Debugging ====================================================
% Commented out, since they are not currently used.
%
% % Prints the top (string) of the stack, without popping it.
% FUNCTION {shows}
% { duplicate$ "::::  `" swap$ * "'" * top$
% }
%
% % Pops and prints the whole stack.
% FUNCTION {showstack}
% {"### STACK #################################################" top$
%  stack$
%  "### ENDSTACK ##############################################" top$
% }



%%%==2B. Boolean operators ============================================
% Of one numerical argument. Returns 0 [1] if the argument is !=0 [0].
FUNCTION {not}
{   { #0 }
    { #1 }
  if$
}

% Of two numerical arguments. Returns 0 [1] if these arguments aren't
% both 1 [are both 1].
FUNCTION {and}
{   'skip$
    { pop$ #0 }
  if$
}

% Of two numerical arguments. Returns 0 [1] if these arguments are
% both 0 [aren't both 0].
FUNCTION {or}
{   { pop$ #1 }
    'skip$
  if$
}



%%%==2C. Other ========================================================
% Of one string argument. If this is nonempty, returns it intact.
% Otherwise, returns "".
FUNCTION {field.or.null}
{ duplicate$ empty$
    { pop$ "" }
    'skip$
  if$
}

% Issues a warning. For usage, see some place where it is used.
FUNCTION {either.or.check}
{ empty$
    'pop$
    { "can't use both " swap$ * " fields in " * cite$ * warning$ }
  if$
}

% Issues a warning. For usage, see some place where it is used.
FUNCTION {missing.warning}
{ "missing " swap$ * " in " * cite$ * warning$
}








%%%====================================================================
%%%==3== Output to .bbl ===============================================
%%%====================================================================

% Writes to the file the top of the stack and a new line character.
FUNCTION {write.line}
{ write$ newline$
}

% Pushes onto the stack the name of the \bibitem-like command that
% should introduce the entry in the `thebibliography' environment,
% in the .bbl file. In every group of successive entries that have
% the same author(s)/editor(s), the first one (same.flag=0) is
% introduced with a "\bibfitem" command, while the rest (same.flag=1)
% are introduced with a "\bibritem" command.
FUNCTION {command.name}
{ same.flag #0 =
    { "\bibfitem" }
    { "\bibritem" }
  if$
}

% Of no argument. Writes to the .bbl file the header of the bibitem
% for the current entry. This is how a bibitem construction starts.
% In correlation with function fin.entry that follows, output.bibitem
% should have been called "start.entry" instead.
%
% The intended syntax of the \bibfitem, \bibritem commands is:
%        \bib?item 1. {citation key}        (cite$)
%                  2. {guys-list}           (name.label.one,..,ten)
% (!)              3. {year}                (year)
%                  4. {tag}                 (xtra.label)
%                  5. {`number' of editors} (nofeditors)
%                  6. {hardcite}            (hardcite)
%                  7. {hardlist}            (hardlist)
FUNCTION {output.bibitem}
{ newline$
  command.name "{" * cite$ * "}" *    write.line
  "{" name.label.one *                write$
      name.label.two                  write$
      name.label.three                write$
      name.label.four                 write$
      name.label.five                 write$
      name.label.six                  write$
      name.label.seven                write$
      name.label.eight                write$
      name.label.nine                 write$
      name.label.ten "}" *            write.line
  "{" year field.or.null * "}" *      write$
  "{" xtra.label * "}" *              write$
  "{" nofeditors int.to.str$ * "}" *  write.line
  "{" hardcite field.or.null * "}" *  write$
  "{" hardlist field.or.null * "}" *  write.line
  #1 'at.bibitem.start :=
  ""
  % This last empty string is the first thing that will be written
  % the next time write$ is called.  Done this way because each
  % item is saved on the stack until we find out what punctuation
  % should be added after it.  Therefore we need an empty first item.
}

% Of one string argument, the last part of a bibitem. It adds the
% proper punctuation and writes it to the .bbl file. It also outputs
% the sort key of the entry. This is how a bibitem construction ends.
FUNCTION {fin.entry}
{ add.period$  write.line
  "\TheSortKeyIs{" sort.key$ * "}" * write.line
}

% Of one string argument, which should be a new, non null block of
% the current bibitem. Let it be the i'th block (i=1,2,..).
%
% At the moment the function is called, the element of the stack
% that lies immediately under this argument is a string containing
% the (i-1)'th bibitem block. [If i=1, then the argument of the
% function is the first bibitem block and immediately under it in
% the stack there is an empty string (""), put there by the second
% last line of output.bibitem.]
%
% So, the first line pops the i'th block off the stack, to reveal
% the (i-1)'th one. The last line pushes it back onto the stack.
% Then:
%    --If i=1  (if at.bibitem.start=true)
%      The (i-1)'th block is "". It is just popped off the stack.
%    --If i>1  (if at.bibitem.start=false)
%      The function knows that the (i-1)'th block will be followed
%      by a nonempty one (the i'th one). Therefore, it can output to
%      the .bbl file this (i-1)'th block and also a comma, to separate
%      the two consequtive blocks from each other.
%      There are two exceptions to the comma insertion:
%         1. When the i'th block is a "\yearmagic{,}{"-starting one
%            then the comma will be inserted by the expansion of the
%            \yearmagic macro (if necessary).
%         2. When the (i-1)'th block is a "\guysmagic"-starting one,
%            then again the comma will be inserted by the macro.
%
% This is how the intermediate steps of a bibitem construction are
% performed. The two `output' functions that follow, call this one.
FUNCTION {output.nonnull}
{ 's :=
  at.bibitem.start #1 =
    { pop$
      #0 'at.bibitem.start :=
    }
    { s #1 #14 substring$ "\yearmagic{,}{" =
        { write$ }
        { 'r :=
           r #1 #11 substring$ "\guysmagic{" =
             { r "  " * write$ }
             { r ", " * write$ }
           if$
        }
      if$
    }
  if$
  s
}

% Of one string argument. Checks to see if this is empty. If not, it
% calls output.nonnull to write it out.
FUNCTION {output}
{ duplicate$ empty$
    'pop$
    'output.nonnull
  if$
}

% Of two string arguments, a field name (held by t) and its value. If
% the value is nonnull, calls output.nonnull. Otherwise, it gives a
% warning on-screen that the given field is empty.
FUNCTION {output.check}
{ 't :=
  duplicate$ empty$
    { pop$ t missing.warning }
    'output.nonnull
  if$
}








%%%====================================================================
%%%==4== Formatting ===================================================
%%%====================================================================



%%%==4A. General auxiliary functions ==================================
% Of one string argument, e.g., s. Returns "{\em" * s * "}", if s is
% not null. Returns "" if s is null.
FUNCTION {emphasize}
{ duplicate$ empty$
    { pop$ "" }
    { "{\em " swap$ * "}" * }
  if$
}

% Of two string arguments, a font name t and a field name s. Returns
% "{" * t * " " * s * "}". For example,
%      title "\em" apply.font
% is equivalent to
%      title emphasize .
FUNCTION {apply.font}
{ 't :=
  duplicate$ empty$
    { pop$ "" }
    { "{" t * " " * swap$ * "}" * }
  if$
}

% Used to make sure page ranges get the TeX code (two hyphens) for
% en-dashes.
FUNCTION {n.dashify}
{ 't :=
  ""
    { t empty$ not }
    { t #1 #1 substring$ "-" =
	{ t #1 #2 substring$ "--" = not
	    { "--" *
	      t #2 global.max$ substring$ 't :=
	    }
	    {   { t #1 #1 substring$ "-" = }
		{ "-" *
		  t #2 global.max$ substring$ 't :=
		}
	      while$
	    }
	  if$
	}
	{ t #1 #1 substring$ *
	  t #2 global.max$ substring$ 't :=
	}
      if$
    }
  while$
}

% Of one string argument, which should be the contents of the
% pages field. Decides whether this is a representation of one
% or of many pages (so that p. or pp. is used, see format.pages).
FUNCTION {multi.page.check}
{ 't :=
  #0 'multiresult :=
    { multiresult not
      t empty$ not
      and
    }
    { t #1 #1 substring$
      duplicate$ "-" =
      swap$ duplicate$ "," =
      swap$ "+" =
      or or
	{ #1 'multiresult := }
	{ t #2 global.max$ substring$ 't := }
      if$
    }
  while$
  multiresult
}

% Of two string arguments. Connects them with a ~ if the second
% one is less than 3 letters long, otherwise it puts an ordinary
% space. Returns this concatenation.
FUNCTION {tie.or.space.connect}
{ duplicate$ text.length$ #3 <
    { "~" }
    { " " }
  if$
  swap$ * *
}

% Of one string argument. Returns it augmented by a space
% character. If the argument is empty, simply returns it.
FUNCTION {add.space.if.necessary}
{ duplicate$ "" =
    'skip$
    { " " * }
  if$
}

% Of one string argument, which must be name. Formats this name as:
% 	First von Last, Jr.
% (i.e., first name first, no abbreviating to initials).
FUNCTION {format.names}
{ 's :=
  #1 'nameptr :=
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { s nameptr "{ff~}{vv~}{ll}{, jj}" format.name$ 't :=
      nameptr #1 >
	{ namesleft #1 >
	    { ", " * t * }
	    { numnames #2 >
		{ "," * }
		'skip$
	      if$
	      t "others" =
		{ " \bibetal " * }
		{ " \biband{} " * t * }
	      if$
	    }
	  if$
	}
	't
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

% Checks whether a misc entry is completely empty.
FUNCTION {empty.misc.check}
{ author empty$ title empty$ howpublished empty$
  month empty$ year empty$ note empty$
  and and and and and
  key empty$ not and
    { "all relevant fields are empty in " cite$ * warning$ }
    'skip$
  if$
}



%%%==4B. Formatting of fields =========================================

% language is an extra field. Format as: (<language>)
FUNCTION {format.language}
{ language empty$
    { "" }
    { " (" language * ")" * }
  if$
}

FUNCTION {format.authors}
{ author empty$
    { "" }
    { "\guysmagic{"
      same.flag #1 =
        {"\bysame"}
        { author format.names "\scshape" apply.font }
      if$
      * "}" *
    }
  if$
}

FUNCTION {format.editors}
{ editor empty$
    { "" }
    { "\guysmagic{"
      editor format.names *
      editor num.names$ #1 >
        { " (editors)" }
        { " (editor)"  }
      if$
      * "}" *
    }
  if$
}

FUNCTION {format.nonauthor.editors}
{ editor empty$
    { "" }
    { editor format.names
      editor num.names$ #1 >
	{ ", editors" * }
	{ ", editor" * }
      if$
    }
  if$
}

FUNCTION {format.title}
{ title empty$
    { "" }
    { title "t" change.case$ emphasize }
  if$
}

FUNCTION {format.booktitle}
{ title empty$
    { "" }
    { title "t" change.case$ "\bfseries\itshape" apply.font }
  if$
}

% (ynm) If the value of the journal field is either "The Journal
% of Symbolic Logic" or "Journal of Symbolic Logic", it is replaced
% with \jslname. If it is "The Bulletin of Symbolic Logic" or
% "Bulletin of Symbolic Logic", it is replaced with \bslname. Then,
% asl.cls defines these commands so that the correct output is given,
% depending on the publications
FUNCTION {format.journal}
{ journal empty$
    { "journal name" missing.warning "" }
    { journal "The Journal of Symbolic Logic" =
      journal "Journal of Symbolic Logic" =
      or
       { "{\normalfont \jslname}" }
       { journal "The Bulletin of Symbolic Logic" =
         journal "Bulletin of Symbolic Logic" =
         or
          { "{\normalfont \bslname}" }
          { journal "\bfseries\itshape" apply.font }
        if$
       }
     if$
    }
  if$
}

% (+) For the phrase "vol." we don't add a following ~ because
% absolute prohibition of a line break there might be too stringent
% (consider that the volume number might be three or even more
% digits). Instead we use \weaktie.
FUNCTION {format.vol.year}
{ volume empty$
    { ""            %'skip$  :here lay the bug!
      "," 's :=     %remember the \yearmagic parameter.
    }
    { "vol.\weaktie " volume *
      ""  's :=     %remember the \yearmagic parameter.
    }
  if$
  year empty$
    { "year" missing.warning }
    { "\yearmagic{" * s * "}{(" * year * ")}" * }
  if$
}

% Formats the issue number of a journal article.
FUNCTION {format.number}
{ number empty$
    { "" }
    { "no.\weaktie " number * }
  if$
}

% Formats miscellaneous dates
FUNCTION {format.date}
{ year empty$
    { month empty$
	{ "" }
	{ "there's a month but no year in " cite$ * warning$
	  month
	}
      if$
    }
    { month empty$
	{ "\yearmagic{,}{" year * "}" * }
	{ month "\yearmagic{}{" * year * "}" * }
      if$
    }
  if$
}

% The volume, series and number information is sort of tricky.
% This code handles it as follows:
% If the series is present, and the volume, but not the number,
%   then we do "{\em Book title}, Series Name, vol. 000"
% If the series is present, and the number, but not the volume,
%   then we do "{\em Book title}, Series Name, no. 000"
% If the series is present, and both number and volume,
%   then we do "{\em Book title}, vol. XX, Series Name, no. 000"
% Finally, if the series is absent,
%   then we do "{\em Book title}, vol. XX"
%   or         "{\em Book title}, no. 000"
%   and if both volume and number are present, give a warning message.
FUNCTION {format.bookvolume.series.number}
{ volume empty$
    % If the volume is EMPTY:
    { "" % Push the empty string as a placeholder in case everything else
         % is empty too.
      series empty$
        'skip$
        { pop$ series } % if series is not empty put in stack
      if$
      number empty$
        'skip$
        { duplicate$ empty$ % if no preceding material,
            'skip$          % do nothing, otherwise
            { ", " * }      % add a comma and space to separate.
          if$
          "no." number tie.or.space.connect * % add the number information
        }
      if$
    }
    % If the volume is NOT EMPTY:
    { "vol." volume tie.or.space.connect % vol. XX
      number empty$
        { series empty$
            'skip$
            { series ", " * swap$ *}     % Series Name, vol. XX
          if$
        }
        { series empty$
            { "can't use both volume and number if series info is missing"
              warning$
              "in BibTeX entry type `" type$ * "'" * top$
            }
            { ", " * series * ", no." * number tie.or.space.connect }
          if$
        }
      if$
    }
  if$
}

% Used by inproceedings entry types
FUNCTION {format.inproc.title.address.editors}
{ booktitle empty$
    { "" }
    { booktitle "t" change.case$ "\bfseries\itshape" apply.font }
  if$
  % We add parentheses around the address
  % (place where conference was held).
  address empty$
    'skip$
    { add.space.if.necessary "(" * address * ")" * }
  if$
  % Likewise we add parentheses around the editors' names.
  editor empty$
    'skip$
    { add.space.if.necessary "(" * format.nonauthor.editors * ")" * }
  if$
}

% Similar to format.inproc... but omits the address. For collections
% that are not proceedings volumes.
FUNCTION {format.incoll.title.editors}
{ booktitle empty$
    { "" }
    { booktitle "t" change.case$ "\bfseries\itshape" apply.font }
  if$
  % We add parentheses around the editors' names.
  editor empty$
    'skip$
    { add.space.if.necessary "(" * format.nonauthor.editors * ")" * }
  if$
}

% Desired output for format.number.series:
%	Lecture Notes in Math., no.~1224
FUNCTION {format.number.series}
{ series empty$
    { number empty$
        { "" }
        { "there's a number but no series in " cite$ * warning$ }
      if$
    }
    { series
      number empty$
        'skip$
        { ", no.\weaktie " * number * }
      if$
    }
  if$
}

FUNCTION {format.edition}
{ edition empty$
    { "" }
    { at.bibitem.start #0 =
	{ edition "l" change.case$ " ed." * }
	{ edition "t" change.case$ " ed." * }
      if$
    }
  if$
}

FUNCTION {format.pages}
{ pages empty$
    { "" }
    { pages multi.page.check
	{ "pp.\weaktie " pages n.dashify * }
	{ "p.\weaktie " pages * }
      if$
    }
  if$
}

FUNCTION {format.book.pages}
{ format.pages
}

FUNCTION {format.chapter.pages}
{ chapter empty$
    'format.pages
    { type empty$
	{ "ch.\weaktie " }
	{ type "l" change.case$ " " * }
      if$
      chapter *
      pages empty$
	'skip$
	{ ", " * format.book.pages * }
      if$
    }
  if$
}

FUNCTION {format.thesis.type}
{ type empty$
    'skip$
    { pop$
      type "t" change.case$
    }
  if$
  "\bfseries\itshape" apply.font
}

FUNCTION {format.tr.number}
{ type empty$
    { "Technical Report" }
    'type
  if$
  number empty$
    { "t" change.case$ }
    { number tie.or.space.connect }
  if$
  "\bfseries\itshape" apply.font
}

% The format.crossref functions haven't been paid much attention
% at the present time (June 1990) and could probably use some
% work.  MJD

FUNCTION {format.article.crossref}
{ key empty$
    { journal empty$
	{ "need key or journal for " cite$ * " to crossref " * crossref *
	  warning$
	  ""
	}
	{ "In " journal * }
      if$
    }
    { "In " key * }
  if$
  " \cite{" * crossref * "}" *
}

FUNCTION {format.crossref.editor}
{ editor #1 "{vv~}{ll}" format.name$
  editor num.names$ duplicate$
  #2 >
    { pop$ " \bibetal{}" * }
    { #2 <
	'skip$
	{ editor #2 "{ff }{vv }{ll}{ jj}" format.name$ "others" =
	    { " \bibetal{}" * }
	    { " \biband{} " * editor #2 "{vv~}{ll}" format.name$ * }
	  if$
	}
      if$
    }
  if$
}

FUNCTION {format.book.crossref}
{ volume empty$
    { "empty volume in " cite$ * "'s crossref of " * crossref * warning$
      "In "
    }
    { "Vol." volume tie.or.space.connect
      " of " *
    }
  if$
  editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
	{ series empty$
	    { "need editor, key, or series for " cite$ * " to crossref " *
	      crossref * warning$
	      "" *
	    }
	    { series * }
	  if$
	}
	{ key * }
      if$
    }
    { format.crossref.editor * }
  if$
  " \cite{" * crossref * "}" *
}

FUNCTION {format.incoll.inproc.crossref}
{ editor empty$
  editor field.or.null author field.or.null =
  or
    { key empty$
	{ booktitle empty$
	    { "need editor, key, or booktitle for " cite$ * " to crossref " *
	      crossref * warning$
	      ""
	    }
	    { "In {\em " booktitle * "\/}" * }
	  if$
	}
	{ "In " key * }
      if$
    }
    { "In " format.crossref.editor * }
  if$
  " \cite{" * crossref * "}" *
}



%%%==4C. Formatting of entries ========================================

FUNCTION {article}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  crossref missing$
    { format.journal output
      format.vol.year output
      format.number output
      format.pages "pages" output.check
    }
    { format.article.crossref output.nonnull
      format.pages output
    }
  if$
  format.language *
  note output
  fin.entry
}

FUNCTION {book}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check }
    { format.authors output.nonnull
      crossref missing$
	{ "author and editor" editor either.or.check }
	'skip$
      if$
    }
  if$
  format.booktitle "title" output.check
  format.edition output
  crossref missing$
    { format.bookvolume.series.number output
      publisher "publisher" output.check
      address output
    }
    { format.book.crossref output.nonnull
    }
  if$
  format.date "year" output.check
  format.language *
  note output
  fin.entry
}

FUNCTION {booklet}
{ output.bibitem
  format.authors output
  format.title "title" output.check
  howpublished output
  address output
  format.date output
  note output
  fin.entry
}

FUNCTION {conference}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  crossref missing$
    { format.inproc.title.address.editors "booktitle" output.check
      format.bookvolume.series.number output
      organization output
      publisher output
      format.date "year" output.check
    }
    { format.incoll.inproc.crossref output.nonnull
    }
  if$
  note output
  format.book.pages output
  format.language *
  fin.entry
}

FUNCTION {inbook}
{ output.bibitem
  author empty$
    { format.editors "author and editor" output.check }
    { format.authors output.nonnull
      crossref missing$
	{ "author and editor" editor either.or.check }
	'skip$
      if$
    }
  if$
  title "title" output.check
  crossref missing$
    { format.bookvolume.series.number output
      format.chapter.pages "chapter and pages" output.check
      format.number.series output
      publisher "publisher" output.check
      address output
    }
    { format.chapter.pages "chapter and pages" output.check
      format.book.crossref output.nonnull
    }
  if$
  format.edition output
  format.date "year" output.check
  format.book.pages output
  format.language *
  note output
  fin.entry
}

FUNCTION {incollection}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  crossref missing$
    { format.incoll.title.editors "booktitle" output.check
      format.bookvolume.series.number output
      publisher "publisher" output.check
      address output
      format.edition output
      format.date "year" output.check
    }
    { format.incoll.inproc.crossref output.nonnull
    }
  if$
  note output
  format.book.pages output
  format.language *
  fin.entry
}

FUNCTION {inproceedings}
{ conference
} 

FUNCTION {manual}
{ output.bibitem
  author empty$
    { organization empty$
	'skip$
	{ organization output.nonnull
	  address output
	}
      if$
    }
    { format.authors output.nonnull }
  if$
  format.title "title" output.check
  author empty$
    { organization empty$
	{ address output }
	'skip$
      if$
    }
    { organization output
      address output
    }
  if$
  format.edition output
  format.date output
  note output
  fin.entry
}

FUNCTION {mastersthesis}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  "Master's thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  format.date "year" output.check
  note output
  fin.entry
}

FUNCTION {misc}
{ output.bibitem
  format.authors output
  format.title output
  howpublished output
  format.date output
  note output
  format.book.pages output
  fin.entry
  empty.misc.check
}

FUNCTION {phdthesis}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  "Ph.D. thesis" format.thesis.type output.nonnull
  school "school" output.check
  address output
  format.date "year" output.check
  note output
  format.book.pages output
  fin.entry
}

FUNCTION {proceedings}
{ output.bibitem
  editor empty$
    { organization output }
    { format.editors output.nonnull }
  if$
  format.title "title" output.check
  format.bookvolume.series.number output
  address empty$
    { editor empty$
        'skip$
	{ organization output }
      if$
      publisher output
      format.date "year" output.check
    }
    { address output.nonnull
      editor empty$
	'skip$
	{ organization output }
      if$
      publisher output
      format.date "year" output.check
    }
  if$
  note output
  fin.entry
}

FUNCTION {techreport}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  format.tr.number output.nonnull
  institution "institution" output.check
  address output
  format.date "year" output.check
  note output
  fin.entry
}

FUNCTION {unpublished}
{ output.bibitem
  format.authors "author" output.check
  format.title "title" output.check
  note "note" output.check
  format.date output
  fin.entry
}

FUNCTION {default.type}
{ misc
}







%%%====================================================================
%%%==5== Input ========================================================
%%%====================================================================

READ








%%%====================================================================
%%%==6== Sort =========================================================
%%%====================================================================

% SORTING
%
% To sort the list of entries, we must first compute the sort.key$
% (this is an entry field, implicitly defined for all entries) by
% executing function "presort" on each entry. Then, based on the
% sort.key$ values, the SORT command can sort the entire list. So,
% the code is
%    ITERATE {presort}    % Calculate the sort.key$'s.
%    SORT                 % Use the sort.key$'s to sort the list.
% in section 6C.
%
% For each entry, the sort.key$ is calculated as follows:
%   -- If the hardsort field was defined in this entry: Then the
% calculation of sort.key$ is easy: simply assign to it the value of
% the hardsort field. This way we can manually control the position
% of any entry in the bibliography list. (For each entry the .bbl file
% will always contain the value of its sort.key$ as an argument to the
% gobbling macro \TheSortKeyIs.)
%   -- If the hardsort field was not defined in this entry: Then
% the sort.key$ is the concatenation of a number of `sortify'ed strings
% (see function `sortify' below), with multiple blanks between them.
% [ This makes, e.g., "brinch  per" come before "brinch hansen  per". ]
% The fields used here are: the author names [or editor names or
% organization (with a leading "The " removed) or key field, depending
% on entry type and on what's empty], followed by year, followed by the
% first bit of the title (chopping off a leading "The ", "A ", or
% "An "). Names are formatted as:
%	Von Last First Junior.
% The names within a part will be separated by a single blank (such as
% "brinch hansen"), two will separate the name parts themselves (except
% the von and last), three will separate the names, four will separate
% the names from year (and from label, if alphabetic), and four will
% separate year from title.



%%%==6A. General purpose functions ====================================

% Of one string argument. Returns in purify$ed and in lower case.
FUNCTION {sortify}
{ purify$
  "l" change.case$
}

% Of three arguments, a string w, an integer len, a string s. Returns
% either s or, if the first len letters of s equals w, it returns the
% part of s after w.
FUNCTION {chop.word}
{ 's :=
  'len :=
  s #1 len substring$ =    %compares with w (which is in the stack).
    { s len #1 + global.max$ substring$ }
    's
  if$
}

% Of one string argument, that should be in BibTeX name format. Returns
% a string containing "   "-separated names in the format described
% above.
FUNCTION {sort.format.names}
{ 's :=
  #1 'nameptr :=
  ""
  s num.names$ 'numnames :=
  numnames 'namesleft :=
    { namesleft #0 > }
    { nameptr #1 >
	{ "   " * }         % Exactly three spaces in the blank string.
	'skip$
      if$
      s nameptr "{vv{ } }{ll{ }}{  ff{ }}{  jj{ }}" format.name$ 't :=
      nameptr numnames = t "others" = and
	{ "et al" * }
	{ t sortify * }
      if$
      nameptr #1 + 'nameptr :=
      namesleft #1 - 'namesleft :=
    }
  while$
}

% Of one string argument, a title. Returns the string after chopping
% off any "A ", "An ", "The " -prefix, purifying, case lowering and
% to-global.max$ chopping.
FUNCTION {sort.format.title}
{ 't :=
  "A " #2
    "An " #3
      "The " #4 t chop.word
    chop.word
  chop.word
  sortify
  #1 global.max$ substring$
}



%%%==6B. Calculation of the sort.key$ =================================

FUNCTION {author.sort}
{ author empty$
    { key empty$
	{ "to sort, need author or key in " cite$ * warning$
	  ""
	}
	{ key sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.editor.sort}
{ author empty$
    { editor empty$
	{ key empty$
	    { "to sort, need author, editor, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ editor sort.format.names }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {author.organization.sort}
{ author empty$
    { organization empty$
	{ key empty$
	    { "to sort, need author, organization, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ "The " #4 organization chop.word sortify }
      if$
    }
    { author sort.format.names }
  if$
}

FUNCTION {editor.organization.sort}
{ editor empty$
    { organization empty$
	{ key empty$
	    { "to sort, need editor, organization, or key in " cite$ * warning$
	      ""
	    }
	    { key sortify }
	  if$
	}
	{ "The " #4 organization chop.word sortify }
      if$
    }
    { editor sort.format.names }
  if$
}

FUNCTION {calc.sort.key}
{ type$ "book" =
  type$ "inbook" =
  or
    'author.editor.sort
    { type$ "proceedings" =
	'editor.organization.sort
	{ type$ "manual" =
	    'author.organization.sort
	    'author.sort
	  if$
	}
      if$
    }
  if$
  "    " *                   % Exactly four spaces in the blank string.
  year field.or.null sortify *
  hardxtra field.or.null sortify *         % Insert the hardxtra field.
  "    " *                   % Exactly four spaces in the blank string.
  title field.or.null sort.format.title *
  #1 entry.max$ substring$
  'sort.key$ :=
}

FUNCTION {presort}
{ hardsort missing$
    { calc.sort.key }
    { hardsort 'sort.key$ := }
  if$
}



%%%==6C. Sorting ======================================================

ITERATE {presort}
SORT








%%%====================================================================
%%%==7== Calculate ====================================================
%%%====================================================================



%%%==7A. General functions ============================================

% Returns the author, if nonempty, otherwise the editor, if nonempty,
% otherwise the empty string.
FUNCTION {author.editor.null}
{ author empty$
    { editor empty$
        { "" }
        'editor
      if$
    }
    'author
  if$
}

% Of one string argument. Returns this, if not "". Otherwise, the
% dummy string "abcxyz" is returned.
FUNCTION {string.or.dummy}
{ 's :=
  s "" =
    { "abcxyz" }
    { s }
  if$
}



%%%==7B. Calculate same.flag ==========================================

% Just prepares the two string variables needed.
FUNCTION {init.calc.same.flag}
{ "abcxyz" 'prev.author :=
  ""       'curr.author :=
}

% Calculates the `author' of the current entry into curr.author. Then
% compares this `author' with the one of the previous entry. If they
% are the same, then \bysame should appear in the current entry. The
% flag to mark it is the same.flag entry variable.
FUNCTION {calc.same.flag}
{ author.editor.null 'curr.author :=
  curr.author prev.author =
    { #1 'same.flag := }
    { #0 'same.flag :=
      curr.author string.or.dummy 'prev.author :=
    }
  if$
}

EXECUTE {init.calc.same.flag}

ITERATE {calc.same.flag}



%%%==7C. Calculate xtra.label =========================================

% Just initialize the variables.
FUNCTION {init.calc.xtra.label}
{ "abcxyz" 'prev.author :=
  "abcxyz" 'prev.year   :=
  ""       'curr.author :=
  ""       'curr.year   :=
  "a"      'next.xtra   :=
}

FUNCTION {calc.xtra.label.fore}
{ author.editor.null 'curr.author :=
  year field.or.null 'curr.year :=
  curr.author prev.author =
  curr.year   prev.year   =
  and
    { next.xtra chr.to.int$ #1 + int.to.chr$ 'next.xtra :=
      next.xtra 'xtra.label :=
    }
    { "a" 'next.xtra :=
      "" 'xtra.label :=
      curr.author string.or.dummy 'prev.author :=
      curr.year   string.or.dummy 'prev.year   :=
    }
  if$
}

FUNCTION {calc.xtra.label.back}
{ "b" next.xtra =
    { "a" 'xtra.label := }
    'skip$
  if$
  xtra.label 'next.xtra :=
}

EXECUTE {init.calc.xtra.label}
ITERATE {calc.xtra.label.fore}
EXECUTE {init.calc.xtra.label}
REVERSE {calc.xtra.label.back}



%%%==7D. Calculate name.label =========================================

% Sets all name.label parts to the empty string. No part is active.
FUNCTION {nl.init}
{ "" 'name.label.one   :=
  "" 'name.label.two   :=
  "" 'name.label.three :=
  "" 'name.label.four  :=
  "" 'name.label.five  :=
  "" 'name.label.six   :=
  "" 'name.label.seven :=
  "" 'name.label.eight :=
  "" 'name.label.nine  :=
  "" 'name.label.ten   :=
  #0 'active.nl.part   :=
}

% Of one string argument, t. Appends it to the currently active
% part of name.label.
FUNCTION {nl.stick}
{ 't :=
    #1  active.nl.part = { name.label.one   t * 'name.label.one   := }
  { #2  active.nl.part = { name.label.two   t * 'name.label.two   := }
  { #3  active.nl.part = { name.label.three t * 'name.label.three := }
  { #4  active.nl.part = { name.label.four  t * 'name.label.four  := }
  { #5  active.nl.part = { name.label.five  t * 'name.label.five  := }
  { #6  active.nl.part = { name.label.six   t * 'name.label.six   := }
  { #7  active.nl.part = { name.label.seven t * 'name.label.seven := }
  { #8  active.nl.part = { name.label.eight t * 'name.label.eight := }
  { #9  active.nl.part = { name.label.nine  t * 'name.label.nine  := }
  { #10 active.nl.part = { name.label.ten   t * 'name.label.ten   := }
                         { "looong name label in " cite$ *  warning$ }
  if$ } if$ } if$ } if$ } if$ } if$ } if$ } if$ } if$ } if$
}

% Of one string argument, t. Appends it to the next part of the
% name.label, which is made active.
FUNCTION {nl.append}
{ active.nl.part #1 + 'active.nl.part :=
  nl.stick
}

% Of two arguments: a string r (a list of names in BibTeX format) and
% an integer i (>0). Returns a string containing the \guy command that
% corresponds to the i'th name in r. Format of \guy is
% (**)      \guy{first name initials}{first}{von}{last}{junior}
FUNCTION {format.guy}
{ 'i :=
  'r :=
  "\guy{"
  r i "{f.}" format.name$ * "}{" *
  r i "{ff}" format.name$ * "}{" *
  r i "{vv}" format.name$ * "}{" *
  r i "{ll}" format.name$ * "}{" *
  r i "{jj}" format.name$ * "}" *
}

% Of one string argument, a list of names in BibTeX format. Computes a
% string containing the corresponding list of \guy's, with the proper
% punctuation and conjunctor. The string is stored in name.label.one,
% name.label.two, name.label.three through the nl.append function. In
% simple notation:
%
% FUNCTION make.name.label(s)
% { numnames   := num.names$(s)
%   namesleft  := numnames
%   nameptr    := 1
%   nl.init
%   while$(namesleft > 0)
%   { if (nameptr = 1)
%       nl.append( format.guy(s,nameptr) )
%     else
%       if (namesleft = 1)
%         if (format.name$(s,nameptr,"{ff }{vv }{ll}{ jj}") = "others")
%           nl.stick( " et~al." )
%         else
%         { nl.stick( (numnames > 2 ? ", and ":" and ") )
%           nl.append( format.guy(s,nameptr) )
%         }
%       else
%       { nl.stick( ", " )
%         nl.append( format.guy(s,nameptr) )
%       }
%     nameptr   := nameptr + 1
%     namesleft := namesleft - 1
%   }
% }
%
FUNCTION {make.name.label}
{ 's :=
  s num.names$ 'numnames :=
  numnames 'namesleft    :=
  #1 'nameptr            :=
  nl.init
      { namesleft #0 > }
      { nameptr #1 =
          { s nameptr format.guy nl.append }
          { namesleft #1 =
              { s nameptr "{ff }{vv }{ll}{ jj}" format.name$ "others" =
                  { "  et~al." nl.stick }
                  { numnames #2 >
                      { ", and " }
                      { " and " }
                    if$
                    nl.stick
                    s nameptr format.guy nl.append
                  }
                if$
              }
              { ", " nl.stick
                s nameptr format.guy nl.append
              }
            if$
          }
        if$
        nameptr #1 + 'nameptr :=
        namesleft #1 - 'namesleft :=
      }
    while$
}

% Calculates the name.label out of authors/editors. In simple notation:
% name.label := author!=empty ? make.name.label(author):
%               editor!=empty ? make.name.label(editor): ""
FUNCTION {calc.name.label}
{ author empty$
    { editor empty$
        { ""
          "no names at all in " cite$ * warning$
        }
        { editor }
      if$
    }
    { author }
  if$
  make.name.label
}

ITERATE {calc.name.label}



%%%==7E. Calculate nofeditors =========================================

% Extracts the number of editors that appear in the editor field of
% the entry and saves it into nofeditors. It may be called by
% calc.nofeditors; only if the editor field should be consulted.
FUNCTION {extract.nofeditors}
{ editor empty$
    { #0 'nofeditors := }
    { editor num.names$ #1 >
        { #2 'nofeditors := }
        { #1 'nofeditors := }
      if$
    }
  if$
}

% Calculates the nofeditors field. This is like that:
%    if    [ (type$ = "book" or "inbook")  and    (author is empty) ]
%       or [ (type$ = "inproceedings")     and (editor in nonempty) ]
%    then  nofeditors := `number' of names in the editor field
%    else  nofeditors := 0.
% where `number' of names = 0, if the editor field is empty / 1, if
% exactly one name in the editor field/ 2, if more than 2 names in
% the editor field.
%    IMPORTANT: The condition for the if command should be true iff
% the format.editors function will be called for the entry.
FUNCTION {calc.nofeditors}
{       type$ "book" =
        type$ "inbook" =
      or
      author empty$
    and
      type$ "proceedings" =
      editor empty$ not
    and
  or
    { extract.nofeditors }
    { #0 'nofeditors := }
  if$
}

ITERATE {calc.nofeditors}







%%%====================================================================
%%%==8== Output =======================================================
%%%====================================================================



%%%==8A. Functions ====================================================
FUNCTION {begin.bib}
{ preamble$ empty$
    'skip$
    { preamble$ write.line
      newline$ newline$
    }
  if$
  "\begin{thebibliography}{}" write.line
}

FUNCTION {end.bib}
{ newline$
  "\end{thebibliography}" write.line
}



%%%==8B. The actual output ============================================
EXECUTE {begin.bib}
ITERATE {call.type$}
EXECUTE {end.bib}                                                                                            rfffffffffffv