(*
  This file includes modified code from the Ego project
  (https://github.com/verse-lab/ego),
  which is licensed under the GNU General Public License v3.0.

  Modifications © 2025 Migyu Jo.
  See LICENSE.GPL for full license text.
*)
module Id = Id
module Basic = Basic
module Generic = struct
  module Query = Query
  module Scheduler = Scheduler
  include Language
  include Generic
end
