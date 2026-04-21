-- ============================================================
-- 宇宙機ケーススタディ（サブシステム定義）
-- ============================================================
import Examples.Spacecraft.EPS
import Examples.Spacecraft.AOCS
import Examples.Spacecraft.TCS
import Examples.Spacecraft.TTC
import Examples.Spacecraft.Satellite

-- ============================================================
-- 合成サニティテスト（B-6/B-7/B-8）
-- ============================================================
import Examples.Spacecraft.Integration

-- ============================================================
-- F1〜F8 受入条件テスト
-- ============================================================
import Examples.Spacecraft.F1F2Tests
import Examples.Spacecraft.F3F5F6Tests
import Examples.Spacecraft.F8Tests

-- ============================================================
-- B-8d 可変長合成 API 受入条件テスト
-- ============================================================
import Examples.Spacecraft.VariadicComposeTests
