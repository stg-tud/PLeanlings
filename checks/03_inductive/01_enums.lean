/- HINT
Write one line per constructor: `| .monday => .tuesday` and so on.

For `isWeekend`, two cases return `true` and a wildcard `| _ => false`
handles the rest. You can combine patterns: `| .saturday | .sunday => true`.
-/
example : Weekday → Weekday := Weekday.next
example : Weekday → Weekday := Weekday.prev
example : Weekday → Bool := Weekday.isWeekend
example : Weekday.monday.next = .tuesday := rfl
example : Weekday.friday.next = .saturday := rfl
example : Weekday.sunday.next = .monday := rfl
example : Weekday.monday.prev = .sunday := rfl
example : Weekday.saturday.prev = .friday := rfl
example : ∀ d : Weekday, d.next.prev = d := by intro d; cases d <;> rfl
example : ∀ d : Weekday, d.prev.next = d := by intro d; cases d <;> rfl
example : Weekday.monday.next.next.next.next.next.next.next = .monday := rfl
example : Weekday.saturday.isWeekend = true := rfl
example : Weekday.sunday.isWeekend = true := rfl
example : Weekday.monday.isWeekend = false := rfl
example : Weekday.wednesday.isWeekend = false := rfl
example : Weekday.friday.isWeekend = false := rfl
