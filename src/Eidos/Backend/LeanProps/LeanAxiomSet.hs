-- | Re-export of 'Eidos.Pipeline.AxiomSet'.
--
-- The types that used to live here ('Tag', 'SubjectPath', 'AxiomSet', …)
-- have been promoted to the backend-agnostic pipeline so that future
-- backends (Coq, …) can share them.  This module is kept for backward
-- compatibility only.
module Eidos.Backend.LeanProps.LeanAxiomSet
  ( module Eidos.Pipeline.AxiomSet
  ) where

import Eidos.Pipeline.AxiomSet
