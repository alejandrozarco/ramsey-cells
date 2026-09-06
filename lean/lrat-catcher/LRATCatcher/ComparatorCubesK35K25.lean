import LRATCatcher.Cover
import LRATCatcher.K35K25FlatIcnf0
import LRATCatcher.K35K25FlatIcnf1
import LRATCatcher.K35K25FlatIcnf2
import LRATCatcher.K35K25FlatIcnf3
import LRATCatcher.K35K25FlatIcnf4
import LRATCatcher.K35K25FlatIcnf5
import LRATCatcher.K35K25FlatIcnf6
import LRATCatcher.K35K25FlatIcnf7

namespace LRATCatcher.Comparator.K35K25
/-- The flat cover of the verified close of `k35k25_n22` (137,350 leaves), as iCNF text. -/
def flatIcnf : String := icnf0 ++ icnf1 ++ icnf2 ++ icnf3 ++ icnf4 ++ icnf5 ++ icnf6 ++ icnf7
/-- The cube list: `parseICnf` (Cover.lean, ~20 lines) applied to the embedded text. The parser
joins the DIMACS printer in the trusted base; nothing here is evaluated by the kernel. -/
def cubes : List LRATCatcher.Cube := LRATCatcher.parseICnf flatIcnf
end LRATCatcher.Comparator.K35K25
