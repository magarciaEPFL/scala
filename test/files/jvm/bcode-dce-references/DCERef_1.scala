class DCERef_1 {

  def reassignment(rarg: Object) {
    var r = rarg;
    r = r
  }

  def nullToUninitThatGoesUnread() {
    val goesUnread = null
    return goesUnread
  }

  def nullToUninitThatIsUsed() = {
    val goesUnread = null
    goesUnread
  }

  def assignThisToNullSlot() {
    var abc: Object = null
    abc = this
  }

  def assignThisToSlotWithArbitraryRef(arg: Object) {
    var abc = arg
    abc = this
  }

}

