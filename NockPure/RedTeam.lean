/-

  This aggregator collects ONLY the
  batches whose transitive closure is VM-free — the ones that independently re-verify the pure
  language layer:

-/
import Nock.RedTeam.Batch1CoreData
import Nock.RedTeam.Batch2Execution
import Nock.RedTeam.Batch3Reduction
