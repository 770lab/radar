/* ============ RADAR — géoloc partagée en direct ============
 * Chaque visiteur qui accepte la géoloc apparaît sur la carte
 * de tous les autres, tant que sa page reste ouverte.
 * Présence : RTDB /presence/$pid (une clé par onglet, champ owner=uid)
 * + onDisconnect().remove(). Lecture réservée aux visiteurs authentifiés.
 */
(function () {
  'use strict';

  // ---------- Constantes ----------
  var STALE_MS = 75 * 1000;        // au-delà : blip grisé
  var ZOMBIE_MS = 10 * 60 * 1000;  // au-delà : nettoyage du nœud (autorisé par les règles)
  var HEARTBEAT_MS = 25 * 1000;    // refresh du timestamp sans mouvement
  var WRITE_MIN_MS = 2500;         // délai mini entre deux écritures de position
  var WRITE_MIN_METERS = 3;        // ou déplacement mini
  var FIX_FRESH_MS = 90 * 1000;    // au-delà sans fix GPS réel : on cesse de diffuser
  var COORD_DECIMALS = 4;          // précision partagée (~11 m) — pas la position exacte
  var MAX_ACC = 100000;            // borne d'exactitude acceptée par les règles RTDB
  var SHARE_URL = 'https://770lab.com/radar/';

  var CALLSIGNS = [
    'Renard', 'Faucon', 'Lynx', 'Panthère', 'Aigle', 'Loup', 'Colibri',
    'Orque', 'Tigre', 'Cobra', 'Puma', 'Corbeau', 'Gazelle', 'Bison',
    'Phénix', 'Mangouste', 'Vipère', 'Condor', 'Jaguar', 'Belette'
  ];

  // ---------- DOM ----------
  var $ = function (id) { return document.getElementById(id); };
  var elGate = $('gate'), elGateCount = $('gate-count'), elGateError = $('gate-error');
  var elCallsign = $('callsign'), elJoin = $('btn-join'), elReroll = $('btn-reroll');
  var elHud = $('hud'), elHudCount = $('hud-count'), elRoster = $('roster'), elToasts = $('toasts');
  var elMeetup = $('meetup'), elMeetDot = $('meet-dot'), elMeetName = $('meet-name'), elMeetSub = $('meet-sub');
  var elTestbox = $('testbox'), elTestAddr = $('test-addr'), elTestGo = $('test-go'),
      elTestStatus = $('test-status'), elTestRemove = $('test-remove'), elBtnTest = $('btn-test');

  // ---------- État ----------
  var map, mapReady = false, BlipOverlay = null;
  var directionsSvc = null, geocoderSvc = null, placesAutocomplete = null;
  var db, meRef, myUid = null, myPid = null;
  var joined = false;
  var joining = false;
  var gotFirstSnapshot = false;
  var follow = true;
  var suppressMoveEvents = false; // pans programmatiques ≠ drag utilisateur
  var watchId = null, heartbeatTimer = null, repaintTimer = null;
  var serverOffset = 0;
  var lastFix = null;            // dernier GeolocationPosition reçu
  var lastFixAt = 0;             // Date.now() de ce dernier fix GPS réel
  var lastPayload = null;        // dernier objet écrit dans la DB
  var lastWriteAt = 0;
  var people = {};               // pid -> data (clé = session/onglet, pas uid)
  var markers = {};              // pid -> { marker, sig }
  var accCircle = null;
  var knownUids = null;          // pour les toasts arrivée/départ
  var cleanedUids = {};          // zombies déjà nettoyés cette session
  var rosterSig = '';            // évite de reconstruire le roster à l'identique
  var repaintQueued = false;
  var lastRepaintAt = 0;
  // ---- Rendez-vous (« se rejoindre ») ----
  var selectedPid = null;        // la personne que je veux rejoindre
  var meetLine = null;           // trait Leaflet moi -> cible
  var meetSamples = [];          // [{t, d}] pour estimer le temps restant
  var incomingLines = {};        // pid -> trait de ceux qui viennent VERS moi
  var knownIncoming = {};        // pid -> timestamp du dernier toast « X vient te rejoindre »
  var meetNameTxt = '';          // dernier HTML écrit (évite la ré-annonce lecteur d'écran)
  var meetSubTxt = '';
  // ---- Point de test (destination fictive locale, jamais écrite en base) ----
  var TEST_PID = '__test__';
  var testPoint = null;          // { name, lat, lng, hue }
  // ---- Itinéraire piéton réel (suit les rues) ----
  var route = null;              // { coords:[[lat,lng]], distance, duration, from, to, at }
  var routeFetching = false;
  var routeFailed = false;

  // ---------- Utilitaires ----------
  function escapeHtml(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c];
    });
  }

  function randomCallsign() {
    var animal = CALLSIGNS[Math.floor(Math.random() * CALLSIGNS.length)];
    var num = String(Math.floor(Math.random() * 90) + 10);
    return animal + '-' + num;
  }

  function cleanName(raw) {
    return String(raw || '').replace(/\s+/g, ' ').trim().slice(0, 20);
  }

  function newSessionId() {
    if (window.crypto && crypto.randomUUID) return crypto.randomUUID().slice(0, 8);
    return Math.random().toString(36).slice(2, 10);
  }

  function hueFromUid(uid) {
    var h = 0;
    for (var i = 0; i < uid.length; i++) h = (h * 31 + uid.charCodeAt(i)) >>> 0;
    return h % 360;
  }

  function colorFor(hue) { return 'hsl(' + hue + ', 72%, 45%)'; } /* contraste sur fond clair */

  function serverNow() { return Date.now() + serverOffset; }

  function haversine(lat1, lng1, lat2, lng2) {
    var R = 6371000, rad = Math.PI / 180;
    var dLat = (lat2 - lat1) * rad, dLng = (lng2 - lng1) * rad;
    var a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
      Math.cos(lat1 * rad) * Math.cos(lat2 * rad) *
      Math.sin(dLng / 2) * Math.sin(dLng / 2);
    return 2 * R * Math.asin(Math.sqrt(a));
  }

  function formatDist(m) {
    if (!isFinite(m)) return '';
    if (m < 1000) return Math.round(m) + ' m';
    if (m < 10000) return (m / 1000).toFixed(1).replace('.', ',') + ' km';
    return Math.round(m / 1000) + ' km';
  }

  function toast(msg, off, meet) {
    var el = document.createElement('div');
    el.className = 'toast' + (off ? ' toast-off' : '') + (meet ? ' toast-meet' : '');
    el.textContent = msg;
    elToasts.appendChild(el);
    setTimeout(function () { el.remove(); }, 4200);
    while (elToasts.children.length > 4) elToasts.firstChild.remove();
  }

  // ---------- Carte (Google Maps) ----------
  // Style clair épuré : on masque les POI/transports pour ne pas noyer les blips.
  var MAP_STYLE = [
    { featureType: 'poi', stylers: [{ visibility: 'off' }] },
    { featureType: 'transit', stylers: [{ visibility: 'off' }] },
    { featureType: 'road', elementType: 'labels.icon', stylers: [{ visibility: 'off' }] }
  ];

  function initMap() {
    google.maps.importLibrary('maps').then(function (lib) {
      map = new lib.Map(document.getElementById('map'), {
        center: { lat: 46.6, lng: 2.4 }, // France par défaut
        zoom: 6,
        maxZoom: 18,            // évite le zoom « niveau immeuble » (fitBounds de points proches)
        disableDefaultUI: true,
        zoomControl: false,
        gestureHandling: 'greedy',
        clickableIcons: false,
        keyboardShortcuts: false,
        styles: MAP_STYLE
      });
      defineBlipOverlay();
      map.addListener('dragstart', userMovedMap);
      map.addListener('zoom_changed', function () { if (!suppressMoveEvents) userMovedMap(); });
      // Services Places (autocomplétion) + Directions (itinéraire piéton)
      Promise.all([
        google.maps.importLibrary('places'),
        google.maps.importLibrary('routes'),
        google.maps.importLibrary('geocoding')
      ]).then(function () {
        directionsSvc = new google.maps.DirectionsService();
        geocoderSvc = new google.maps.Geocoder();
        initPlaces();
      }).catch(function (e) { console.warn('[radar] libs Google:', e); });
      mapReady = true;
      repaint();
    }).catch(function (e) {
      console.error('[radar] Google Maps:', e);
      elGateCount.textContent = 'Carte indisponible — réessaie plus tard.';
    });
  }

  function userMovedMap() { if (!suppressMoveEvents) follow = false; }

  function panTo(latlng, zoom) {
    if (!map) return;
    suppressMoveEvents = true;
    map.panTo({ lat: latlng[0], lng: latlng[1] });
    map.setZoom(zoom || Math.max(map.getZoom(), 15));
    setTimeout(function () { suppressMoveEvents = false; }, 900);
  }

  // Marqueur HTML personnalisé via OverlayView (blips colorés animés)
  function defineBlipOverlay() {
    function Blip(ll, html, onClick, z) {
      this._ll = ll; this._html = html; this._onClick = onClick; this._z = z || 0;
      this.setMap(map);
    }
    Blip.prototype = new google.maps.OverlayView();
    Blip.prototype.onAdd = function () {
      var d = document.createElement('div');
      d.className = 'blip-ov';
      d.style.zIndex = this._z;
      d.innerHTML = this._html;
      d.addEventListener('click', this._onClick);
      this._div = d;
      this.getPanes().overlayMouseTarget.appendChild(d);
    };
    Blip.prototype.draw = function () {
      if (!this._div) return;
      var proj = this.getProjection();
      if (!proj) return;
      var pt = proj.fromLatLngToDivPixel(this._ll);
      if (!pt) return;
      this._div.style.left = pt.x + 'px';
      this._div.style.top = pt.y + 'px';
    };
    Blip.prototype.onRemove = function () { if (this._div) { this._div.remove(); this._div = null; } };
    Blip.prototype.setLL = function (ll) { this._ll = ll; this.draw(); };
    Blip.prototype.setHtml = function (html) { this._html = html; if (this._div) this._div.innerHTML = html; };
    Blip.prototype.setZ = function (z) { this._z = z; if (this._div) this._div.style.zIndex = z; };
    BlipOverlay = Blip;
  }
  function LL(lat, lng) { return new google.maps.LatLng(lat, lng); }

  // ---------- Rendu des présents ----------
  function markerHtml(p, isMe, stale, selected) {
    var color = colorFor(p.hue || 0);
    var cls = 'blip-inner' + (stale ? ' blip-stale' : '') + (isMe ? ' blip-me' : '') + (selected ? ' blip-selected' : '');
    return '<div class="' + cls + '" style="--c:' + color + '">' +
      '<div class="blip-pulse"></div>' +
      '<div class="blip-dot"></div>' +
      '<div class="blip-label">' + escapeHtml(p.name || '?') + (isMe ? ' (moi)' : '') + '</div>' +
      '</div>';
  }

  // Coalescence : les snapshots RTDB peuvent arriver en rafale
  function repaint() {
    if (repaintQueued) return;
    repaintQueued = true;
    var wait = Math.max(0, 250 - (Date.now() - lastRepaintAt));
    setTimeout(function () {
      repaintQueued = false;
      lastRepaintAt = Date.now();
      doRepaint();
    }, wait);
  }

  function doRepaint() {
    var now = serverNow();
    if (testPoint) people[TEST_PID] = testEntry();  // destination fictive, toujours fraîche
    var uids = Object.keys(people);
    var liveCount = 0;

    uids.forEach(function (uid) {
      var p = people[uid];
      if (!p || typeof p.lat !== 'number' || typeof p.lng !== 'number') return;
      var age = now - (p.t || 0);

      // Nettoyage des zombies (crash sans onDisconnect) — une tentative max
      if (age > ZOMBIE_MS && uid !== myPid && uid !== TEST_PID) {
        if (joined && !cleanedUids[uid]) {
          cleanedUids[uid] = true;
          db.ref('presence/' + uid).remove().catch(function () {});
        }
        removeMarker(uid);
        return;
      }

      var stale = age > STALE_MS;
      if (!stale) liveCount++;
      if (!mapReady) return;   // en attente de la carte : on compte, on ne dessine pas
      var isMe = uid === myPid;
      var selected = uid === selectedPid;
      var z = isMe ? 1000 : (selected ? 800 : 100);
      var sig = [p.name, p.hue, stale, isMe, selected].join('|');
      var entry = markers[uid];

      if (!entry) {
        var ov = new BlipOverlay(LL(p.lat, p.lng), markerHtml(p, isMe, stale, selected),
          (function (id) { return function () { onPersonClick(id); }; })(uid), z);
        markers[uid] = { marker: ov, sig: sig };
      } else {
        entry.marker.setLL(LL(p.lat, p.lng));
        if (entry.sig !== sig) {
          entry.marker.setHtml(markerHtml(p, isMe, stale, selected));
          entry.marker.setZ(z);
          entry.sig = sig;
        }
      }
    });

    // Marqueurs orphelins
    Object.keys(markers).forEach(function (uid) {
      if (!people[uid]) removeMarker(uid);
    });

    // Cercle de précision (moi)
    if (mapReady && joined && lastPayload) {
      var acc = Math.min(lastPayload.acc || 0, 2000);
      if (acc > 15) {
        if (!accCircle) {
          accCircle = new google.maps.Circle({
            map: map, center: { lat: lastPayload.lat, lng: lastPayload.lng }, radius: acc,
            strokeColor: '#0f9d8c', strokeOpacity: 0.35, strokeWeight: 1,
            fillColor: '#0f9d8c', fillOpacity: 0.07, clickable: false
          });
        } else {
          accCircle.setCenter({ lat: lastPayload.lat, lng: lastPayload.lng });
          accCircle.setRadius(acc);
        }
      } else if (accCircle) {
        accCircle.setMap(null);
        accCircle = null;
      }
    }

    renderCounts(liveCount);
    renderRoster(now);
    updateMeetup(now);
    updateIncoming(now);
  }

  function removeMarker(uid) {
    if (markers[uid]) {
      markers[uid].marker.setMap(null);
      delete markers[uid];
    }
  }

  function renderCounts(liveCount) {
    // HUD
    elHudCount.textContent = liveCount + ' en ligne';
    // Écran d'accueil (on ne se compte pas soi-même : pas encore rejoint)
    if (!gotFirstSnapshot) return; // ne pas écraser « Radar injoignable »
    var others = liveCount;
    var txt;
    if (others <= 0) txt = 'Personne sur le radar pour l’instant — sois le premier.';
    else if (others === 1) txt = '1 personne est déjà sur le radar.';
    else txt = others + ' personnes sont déjà sur le radar.';
    elGateCount.textContent = txt;
  }

  function renderRoster(now) {
    if (!joined) return;
    var me = lastPayload;
    var rows = Object.keys(people)
      .filter(function (uid) {
        var p = people[uid];
        return p && typeof p.lat === 'number' && (now - (p.t || 0)) <= ZOMBIE_MS;
      })
      .map(function (uid) {
        var p = people[uid];
        var dist = (me && uid !== myPid) ? haversine(me.lat, me.lng, p.lat, p.lng) : -1;
        return { uid: uid, p: p, dist: dist, isMe: uid === myPid, stale: (now - (p.t || 0)) > STALE_MS };
      })
      .sort(function (a, b) {
        if (a.isMe) return -1;
        if (b.isMe) return 1;
        return a.dist - b.dist;
      });

    var sig = rows.map(function (r) {
      var incoming = r.p.target === myPid;
      return [r.uid, r.p.name, r.p.hue, formatDist(r.dist), r.stale, r.isMe, r.uid === selectedPid, incoming].join('|');
    }).join(';');
    if (sig === rosterSig) return;
    rosterSig = sig;

    elRoster.innerHTML = '';
    rows.forEach(function (r) {
      var isSelected = r.uid === selectedPid;
      var isIncoming = !r.isMe && r.p.target === myPid;
      var chip = document.createElement('button');
      chip.className = 'chip' + (r.isMe ? ' chip-me' : '') + (isSelected ? ' chip-selected' : '') + (isIncoming ? ' chip-incoming' : '');
      chip.type = 'button';
      chip.setAttribute('aria-label',
        (r.p.name || '?') + (r.isMe ? ', moi' : ', à ' + formatDist(r.dist) + (isSelected ? ', rendez-vous en cours' : ', appuie pour rejoindre')));
      if (r.stale) chip.style.opacity = '0.45';

      var dot = document.createElement('span');
      dot.className = 'chip-dot';
      dot.style.setProperty('--c', colorFor(r.p.hue || 0));

      var name = document.createElement('span');
      name.className = 'chip-name';
      name.textContent = r.p.name || '?';

      var dist = document.createElement('span');
      dist.className = 'chip-dist';
      dist.textContent = r.isMe ? 'moi' : (isSelected ? '● rdv' : formatDist(r.dist));

      chip.appendChild(dot);
      chip.appendChild(name);
      chip.appendChild(dist);
      chip.addEventListener('click', (function (id) { return function () { onPersonClick(id); }; })(r.uid));
      elRoster.appendChild(chip);
    });
  }

  // ---------- Toasts arrivée / départ ----------
  function diffPresence(newPeople) {
    var newUids = {};
    Object.keys(newPeople).forEach(function (uid) { newUids[uid] = true; });
    if (knownUids !== null) {
      Object.keys(newUids).forEach(function (uid) {
        if (!knownUids[uid] && uid !== myPid) {
          var p = newPeople[uid];
          if (p && p.name && serverNow() - (p.t || 0) < STALE_MS) {
            toast('📡 ' + p.name + ' apparaît sur le radar');
          }
        }
      });
      Object.keys(knownUids).forEach(function (uid) {
        if (!newUids[uid] && uid !== myPid) {
          var old = people[uid];
          // Pas de toast pour un nœud zombie nettoyé 10 min plus tard
          if (old && old.name && !cleanedUids[uid] && serverNow() - (old.t || 0) < STALE_MS * 2) {
            toast(old.name + ' a quitté le radar', true);
          }
        }
      });
    }
    knownUids = newUids;
  }

  // ---------- Rendez-vous (« se rejoindre ») ----------
  var followBeforeMeet = true;     // suivi carte à restaurer après annulation
  var broadcastTimer = null;

  function onPersonClick(pid) {
    var p = people[pid];
    if (!p) return;
    if (pid === myPid) {
      // Clic sur soi : simple recentrage
      follow = true;
      panTo([p.lat, p.lng], Math.max(map.getZoom(), 15));
      return;
    }
    // Refuser une cible périmée (sinon rdv auto-annulé + toasts contradictoires)
    if ((serverNow() - (p.t || 0)) > STALE_MS) {
      toast((p.name || 'Cette personne') + ' n’est plus assez récent pour un rendez-vous', true);
      return;
    }
    if (selectedPid === pid) {
      clearMeet();                 // reclic sur la même personne = annuler
    } else {
      selectMeet(pid);
    }
  }

  function selectMeet(pid) {
    var p = people[pid];
    if (!p) return;
    if (!selectedPid) followBeforeMeet = follow;  // mémoriser avant de figer le suivi
    selectedPid = pid;
    meetSamples = [];
    route = null; routeFailed = false;            // itinéraire à recalculer pour cette cible
    rosterSig = '';                // forcer le re-rendu des chips (état sélection)
    toast('🎯 Cap sur ' + (p.name || '?') + ' — suis le trait', false, true);
    follow = false;
    // cadrer les deux points (sauf s'ils sont quasi confondus → zoom raisonnable)
    if (lastPayload && map) {
      suppressMoveEvents = true;
      if (haversine(lastPayload.lat, lastPayload.lng, p.lat, p.lng) > 40) {
        var b = new google.maps.LatLngBounds();
        b.extend({ lat: lastPayload.lat, lng: lastPayload.lng });
        b.extend({ lat: p.lat, lng: p.lng });
        map.fitBounds(b, 70);
      } else {
        map.panTo({ lat: p.lat, lng: p.lng });
        map.setZoom(16);
      }
      setTimeout(function () { suppressMoveEvents = false; }, 900);
    }
    broadcastSelection();          // la cible verra « X vient te rejoindre »
    doRepaint();
  }

  function clearMeet(silent) {
    if (!selectedPid) return;
    var prev = people[selectedPid];
    selectedPid = null;
    meetSamples = [];
    rosterSig = '';
    follow = followBeforeMeet;     // restaurer le suivi tel qu'avant la sélection
    hideMeetup();
    if (!silent && prev) toast('Rendez-vous annulé', true);
    broadcastSelection();
    doRepaint();
  }

  // Cible réellement publiable (le point de test reste local, jamais en base)
  function publishableTarget() {
    return (selectedPid && selectedPid !== myPid && selectedPid !== TEST_PID) ? selectedPid : null;
  }

  // Écrit (ou retire) la cible dans ma présence — coalescé pour éviter le spam d'écritures
  function broadcastSelection() {
    if (!joined) return;
    var current = lastPayload ? (lastPayload.target || null) : null;
    if (publishableTarget() === current) return; // rien de nouveau à publier
    if (broadcastTimer) return;                  // une écriture est déjà planifiée
    broadcastTimer = setTimeout(function () {
      broadcastTimer = null;
      var have = lastPayload ? (lastPayload.target || null) : null;
      if (publishableTarget() !== have && joined && lastFix) writeFix(lastFix, true);
    }, 400);
  }

  // temps restant à un rythme donné -> texte
  function formatEta(sec) {
    if (!isFinite(sec) || sec <= 0) return null;
    if (sec < 60) return 'moins d’1 min';
    var m = Math.round(sec / 60);
    if (m < 60) return m + ' min';
    var h = Math.floor(m / 60), mm = m % 60;
    return h + ' h' + (mm ? ' ' + (mm < 10 ? '0' : '') + mm : '');
  }

  // Pente de la distance dans le temps (m/s) par moindres carrés sur la fenêtre.
  // closing = -pente (>0 : on se rapproche).
  function closingSpeed(samples) {
    var n = samples.length;
    if (n < 3) return null;
    var t0 = samples[0].t;
    var sx = 0, sy = 0, sxx = 0, sxy = 0;
    for (var i = 0; i < n; i++) {
      var x = (samples[i].t - t0) / 1000, y = samples[i].d;
      sx += x; sy += y; sxx += x * x; sxy += x * y;
    }
    var denom = n * sxx - sx * sx;
    if (denom === 0) return null;
    var slope = (n * sxy - sx * sy) / denom;   // m/s (distance qui varie)
    return -slope;
  }

  function updateMeetup(now) {
    if (!joined || !selectedPid || !lastPayload) {
      hideMeetup();
      return;
    }
    // Le point de test ne « part » jamais : on le garde frais même si un
    // snapshot vient d'écraser people (updateMeetup peut être appelé hors doRepaint).
    if (selectedPid === TEST_PID && testPoint) people[TEST_PID] = testEntry();
    var target = people[selectedPid];
    // Cible partie / périmée : on annule proprement
    if (!target || typeof target.lat !== 'number' || (now - (target.t || 0)) > STALE_MS) {
      var name = target ? target.name : 'La personne';
      toast((name || 'La personne') + ' n’est plus joignable', true);
      clearMeet(true);
      return;
    }

    var me = [lastPayload.lat, lastPayload.lng];
    var to = [target.lat, target.lng];
    var d = haversine(me[0], me[1], to[0], to[1]); // à vol d'oiseau (détection d'arrivée)

    // Itinéraire piéton réel : on le (re)calcule si besoin (bornes bougé/temps)
    maybeFetchRoute(me, to);
    var routeValid = route && !routeFailed &&
      haversine(me[0], me[1], route.from[0], route.from[1]) < 60 &&
      haversine(to[0], to[1], route.to[0], route.to[1]) < 60;

    var confirmed = target.target === myPid; // rendez-vous mutuel

    var subHtml;
    if (d < 30) {
      subHtml = '<span class="meet-arrived">Vous y êtes 🎉</span>';
    } else if (routeValid) {
      // Distance et durée d'un VRAI trajet à pied qui suit les rues
      var eta = formatEta(route.duration);
      subHtml = formatDist(route.distance) +
        (eta ? ' · ' + eta + ' <span class="meet-eta-src">à pied · par les rues</span>' : '');
    } else {
      // Repli (itinéraire en cours de calcul ou indisponible) : à vol d'oiseau
      var nowMs = Date.now();
      meetSamples.push({ t: nowMs, d: d });
      meetSamples = meetSamples.filter(function (s) { return nowMs - s.t <= 20000; });
      var closing = closingSpeed(meetSamples);
      var span = meetSamples.length >= 2 ? Math.abs(meetSamples[0].d - meetSamples[meetSamples.length - 1].d) : 0;
      var dt = meetSamples.length >= 2 ? (meetSamples[meetSamples.length - 1].t - meetSamples[0].t) / 1000 : 0;
      var reliable = closing !== null && dt >= 10 && span >= 25 && Math.abs(closing) <= 70;
      var approaching = reliable && closing > 0.5;
      if (d > 40000) {
        subHtml = formatDist(d) + ' <span class="meet-eta-src">trop loin pour estimer</span>';
      } else if (reliable && closing < -0.5) {
        subHtml = formatDist(d) + ' <span class="meet-eta-src">vous vous éloignez</span>';
      } else {
        var etaSec = approaching ? d / closing : d / 1.35;
        var src = routeFailed ? (approaching ? 'à ce rythme' : 'à vol d’oiseau') : 'itinéraire…';
        if (etaSec > 3 * 3600) {
          subHtml = formatDist(d) + ' <span class="meet-eta-src">trop loin pour estimer</span>';
        } else {
          var e2 = formatEta(etaSec);
          subHtml = formatDist(d) + (e2 ? ' · ' + e2 + ' <span class="meet-eta-src">' + src + '</span>' : '');
        }
      }
    }

    var nameHtml = 'Cap sur <b>' + escapeHtml(target.name || '?') + '</b>' +
      (confirmed ? ' · <span class="meet-confirm">vous vous rejoignez</span>' : '');

    elMeetDot.style.setProperty('--c', colorFor(target.hue || 0));
    // N'écrire le DOM que si le texte change (évite le matraquage du lecteur d'écran)
    if (nameHtml !== meetNameTxt) { elMeetName.innerHTML = nameHtml; meetNameTxt = nameHtml; }
    if (subHtml !== meetSubTxt) { elMeetSub.innerHTML = subHtml; meetSubTxt = subHtml; }

    elMeetup.classList.remove('hidden');
    document.body.classList.add('has-meet');
    // Le trait suit l'itinéraire réel s'il est prêt (plein), sinon segment direct (pointillé)
    drawMeetLine(routeValid ? route.coords : [me, to], confirmed, !routeValid);
  }

  function hideMeetup() {
    elMeetup.classList.add('hidden');
    document.body.classList.remove('has-meet');
    meetNameTxt = ''; meetSubTxt = '';
    route = null; routeFailed = false;
    clearMeetLine();
  }

  var DASH_SYMBOL = { path: 'M 0,-1 0,1', strokeOpacity: 0.95, strokeWeight: 4, scale: 3 };
  function drawMeetLine(latlngs, confirmed, dashed) {
    if (!map) return;
    var color = confirmed ? '#0f9d8c' : '#f97316';
    var path = latlngs.map(function (c) { return { lat: c[0], lng: c[1] }; });
    if (!meetLine) meetLine = new google.maps.Polyline({ map: map, clickable: false, zIndex: 50 });
    if (dashed) {
      meetLine.setOptions({
        strokeOpacity: 0, strokeColor: color,
        icons: [{ icon: Object.assign({ strokeColor: color }, DASH_SYMBOL), offset: '0', repeat: '14px' }]
      });
    } else {
      meetLine.setOptions({ strokeColor: color, strokeOpacity: 0.95, strokeWeight: confirmed ? 6 : 5, icons: [] });
    }
    meetLine.setPath(path);
  }

  function clearMeetLine() {
    if (meetLine) { meetLine.setMap(null); meetLine = null; }
  }

  // Lignes de ceux qui me visent (« X vient vers moi ») + toast anti-répétition
  var INCOMING_MAX_LINES = 12;     // plafond anti-surcharge (mobile)
  var INCOMING_TOAST_COOLDOWN = 5 * 60 * 1000;
  function updateIncoming(now) {
    var targetingMe = {};          // me vise réellement (indépendant de la fraîcheur)
    var drawn = 0;
    if (mapReady && joined && lastPayload) {
      Object.keys(people).forEach(function (pid) {
        if (pid === myPid) return;
        var p = people[pid];
        if (!p || typeof p.lat !== 'number' || p.target !== myPid) return;
        targetingMe[pid] = true;
        if ((now - (p.t || 0)) > STALE_MS) return;  // trop vieux : ni toast ni trait

        // Toast au plus une fois par période, même si la personne oscille stale/frais
        var last = knownIncoming[pid] || 0;
        if (now - last > INCOMING_TOAST_COOLDOWN) {
          knownIncoming[pid] = now;
          toast('🎯 ' + (p.name || '?') + ' vient te rejoindre', false, true);
        }
        // Pas de doublon avec mon propre trait si je l'ai aussi sélectionné
        if (pid === selectedPid) { removeIncomingLine(pid); return; }
        if (drawn >= INCOMING_MAX_LINES) { removeIncomingLine(pid); return; }
        drawn++;
        var color = colorFor(p.hue || 0);
        var path = [{ lat: p.lat, lng: p.lng }, { lat: lastPayload.lat, lng: lastPayload.lng }];
        if (!incomingLines[pid]) {
          incomingLines[pid] = new google.maps.Polyline({
            map: map, clickable: false, strokeOpacity: 0, zIndex: 40,
            icons: [{ icon: Object.assign({ strokeColor: color }, DASH_SYMBOL, { strokeWeight: 3, scale: 2.5 }), offset: '0', repeat: '13px' }]
          });
        } else {
          incomingLines[pid].setOptions({ icons: [{ icon: Object.assign({ strokeColor: color }, DASH_SYMBOL, { strokeWeight: 3, scale: 2.5 }), offset: '0', repeat: '13px' }] });
        }
        incomingLines[pid].setPath(path);
      });
    }
    // Retirer les traits de ceux qui ne sont plus frais / ne me visent plus
    Object.keys(incomingLines).forEach(function (pid) {
      var p = people[pid];
      if (!p || p.target !== myPid || (now - (p.t || 0)) > STALE_MS || pid === selectedPid) removeIncomingLine(pid);
    });
    // Purger le flag anti-répétition SEULEMENT quand la personne cesse vraiment de me viser
    Object.keys(knownIncoming).forEach(function (pid) {
      if (!targetingMe[pid]) delete knownIncoming[pid];
    });
  }

  function removeIncomingLine(pid) {
    if (incomingLines[pid]) { incomingLines[pid].setMap(null); delete incomingLines[pid]; }
  }

  // ---------- Point de test (destination fictive pour essayer seul) ----------
  function testEntry() {
    return { owner: myUid || '', name: testPoint.name, lat: testPoint.lat, lng: testPoint.lng,
             acc: 0, hue: testPoint.hue, t: serverNow() };
  }

  function toggleTestbox() {
    if (!joined) return;
    var willShow = elTestbox.classList.contains('hidden');
    elTestbox.classList.toggle('hidden', !willShow);
    elBtnTest.classList.toggle('active', willShow);
    if (willShow) {
      elTestRemove.classList.toggle('hidden', !testPoint);
      setTimeout(function () { elTestAddr.focus(); }, 60);
    }
  }

  function setTestStatus(msg, err) {
    elTestStatus.textContent = msg;
    elTestStatus.classList.toggle('err', !!err);
  }

  function placeTestAt(lat, lng, label) {
    testPoint = { name: 'Test', lat: lat, lng: lng, hue: 300 };
    route = null; routeFailed = false;   // recalcul de l'itinéraire pour la nouvelle cible
    elTestRemove.classList.remove('hidden');
    elTestbox.classList.add('hidden');
    elBtnTest.classList.remove('active');
    setTestStatus('');
    if (label) elTestAddr.value = label;
    doRepaint();               // fait apparaître le point tout de suite
    selectMeet(TEST_PID);      // démarre le rendez-vous automatiquement
  }

  // Autocomplétion Google Places directement sur le champ adresse
  function initPlaces() {
    if (!google.maps.places || !google.maps.places.Autocomplete) return;
    placesAutocomplete = new google.maps.places.Autocomplete(elTestAddr, {
      fields: ['geometry', 'name', 'formatted_address']
    });
    placesAutocomplete.addListener('place_changed', function () {
      var pl = placesAutocomplete.getPlace();
      if (pl && pl.geometry && pl.geometry.location) {
        placeTestAt(pl.geometry.location.lat(), pl.geometry.location.lng(), pl.formatted_address || pl.name);
      }
    });
  }

  // « Placer » / Entrée sans choisir de suggestion : géocodage Google du texte tapé
  function placeTest() {
    var q = (elTestAddr.value || '').trim();
    if (!q) { setTestStatus('Entre d’abord une adresse.', true); return; }
    if (!geocoderSvc) { setTestStatus('Carte en cours de chargement…', true); return; }
    elTestGo.disabled = true;
    setTestStatus('Recherche de l’adresse…');
    geocoderSvc.geocode({ address: q, region: 'fr' }, function (results, status) {
      elTestGo.disabled = false;
      if (status === 'OK' && results && results[0]) {
        var loc = results[0].geometry.location;
        placeTestAt(loc.lat(), loc.lng(), results[0].formatted_address);
      } else {
        setTestStatus('Adresse introuvable — précise-la (ville, pays).', true);
      }
    });
  }

  function removeTest() {
    if (selectedPid === TEST_PID) clearMeet(true);
    testPoint = null;
    delete people[TEST_PID];
    removeMarker(TEST_PID);
    knownUids && delete knownUids[TEST_PID];
    elTestAddr.value = '';
    elTestRemove.classList.add('hidden');
    setTestStatus('Point Test retiré.');
    doRepaint();
  }

  // ---------- Itinéraire piéton réel (Google Directions, mode marche) ----------
  function fetchRoute(from, to) {
    if (!directionsSvc) return Promise.resolve(null);
    return directionsSvc.route({
      origin: { lat: from[0], lng: from[1] },
      destination: { lat: to[0], lng: to[1] },
      travelMode: google.maps.TravelMode.WALKING
    }).then(function (res) {
      var r = res && res.routes && res.routes[0];
      var leg = r && r.legs && r.legs[0];
      if (!r || !leg) return null;
      var coords = (r.overview_path || []).map(function (pt) { return [pt.lat(), pt.lng()]; });
      if (coords.length < 2) return null;
      return { coords: coords, distance: leg.distance.value, duration: leg.duration.value };
    }).catch(function () { return null; });
  }

  function maybeFetchRoute(from, to) {
    if (routeFetching) return;
    var nowMs = Date.now();
    if (route && (nowMs - route.at) < 9000 &&
        haversine(from[0], from[1], route.from[0], route.from[1]) < 25 &&
        haversine(to[0], to[1], route.to[0], route.to[1]) < 25) return;   // encore valable
    routeFetching = true;
    var rf = from, rt = to;
    fetchRoute(from, to).then(function (r) {
      routeFetching = false;
      routeFailed = !r;
      if (r) route = { coords: r.coords, distance: r.distance, duration: r.duration, from: rf, to: rt, at: Date.now() };
      if (selectedPid) updateMeetup(serverNow());   // re-rendu avec l'itinéraire frais
    }).catch(function () { routeFetching = false; routeFailed = true; });
  }

  // ---------- Firebase ----------
  function initFirebase() {
    firebase.initializeApp(window.RADAR_CONFIG);
    db = firebase.database();

    db.ref('.info/serverTimeOffset').on('value', function (snap) {
      serverOffset = snap.val() || 0;
    });

    // La lecture de /presence exige d'être authentifié (bloque le scraping
    // anonyme). On s'identifie donc dès le chargement, avant même de rejoindre :
    // cela n'écrit AUCUNE position tant que l'utilisateur ne clique pas.
    ensureAuth().then(subscribePresence).catch(function (err) {
      console.error('[radar] auth init:', err);
      elGateCount.textContent = 'Radar injoignable — réessaie plus tard.';
    });

    // Si rien ne répond, ne pas rester bloqué sur « Connexion au radar… »
    setTimeout(function () {
      if (!gotFirstSnapshot) {
        elGateCount.textContent = 'Radar injoignable — vérifie ta connexion.';
      }
    }, 8000);
  }

  function subscribePresence() {
    // La carte s'anime dès l'accueil (une fois authentifié)
    db.ref('presence').on('value', function (snap) {
      gotFirstSnapshot = true;
      var val = snap.val() || {};
      diffPresence(val);
      people = val;
      if (testPoint) people[TEST_PID] = testEntry();  // ne jamais perdre le point de test
      repaint();
    }, function (err) {
      console.error('[radar] lecture presence:', err);
      elGateCount.textContent = 'Radar injoignable — réessaie plus tard.';
    });

    // Ré-armer la présence après une coupure réseau (si le fix est encore frais)
    db.ref('.info/connected').on('value', function (snap) {
      if (snap.val() === true && joined && meRef && lastPayload) {
        meRef.onDisconnect().remove();
        if (fixIsFresh()) {
          var refresh = Object.assign({}, lastPayload, { t: firebase.database.ServerValue.TIMESTAMP });
          meRef.set(refresh).catch(function () {});
          lastPayload.t = serverNow();
        }
      }
    });
  }

  function ensureAuth() {
    var auth = firebase.auth();
    if (auth.currentUser) return Promise.resolve(auth.currentUser);
    return auth.signInAnonymously().then(function (cred) { return cred.user; });
  }

  // ---------- Partage de position ----------
  function roundCoord(x) {
    var f = Math.pow(10, COORD_DECIMALS);
    return Math.round(x * f) / f;
  }

  function payloadFrom(fix, name, hue) {
    var payload = {
      owner: myUid,
      name: name,
      lat: roundCoord(fix.coords.latitude),
      lng: roundCoord(fix.coords.longitude),
      acc: Math.min(Math.round(fix.coords.accuracy || 0), MAX_ACC),
      hue: hue,
      t: firebase.database.ServerValue.TIMESTAMP
    };
    // Qui je cherche à rejoindre (si sélection active, hors point de test) — sinon clé omise
    var pub = publishableTarget();
    if (pub) payload.target = pub;
    return payload;
  }

  function writeFix(fix, force) {
    if (!joined || !meRef) return;
    var nowMs = Date.now();
    var moved = lastPayload
      ? haversine(lastPayload.lat, lastPayload.lng, fix.coords.latitude, fix.coords.longitude)
      : Infinity;
    if (!force && (nowMs - lastWriteAt < WRITE_MIN_MS || moved < WRITE_MIN_METERS)) return;

    var name = lastPayload ? lastPayload.name : cleanName(elCallsign.value) || randomCallsign();
    var hue = lastPayload ? lastPayload.hue : hueFromUid(myUid);
    var payload = payloadFrom(fix, name, hue);
    lastWriteAt = nowMs;
    lastPayload = Object.assign({}, payload, { t: serverNow() }); // copie locale avec t numérique
    meRef.set(payload).catch(function (err) {
      console.error('[radar] écriture presence:', err);
    });

    if (follow) panTo([payload.lat, payload.lng], Math.max(map.getZoom(), 15));
    repaint();
  }

  // Un fix GPS réel est-il encore assez récent pour qu'on se dise « en direct » ?
  function fixIsFresh() { return lastFixAt > 0 && (Date.now() - lastFixAt) < FIX_FRESH_MS; }

  function geoErrorMessage(err) {
    if (!err) return 'Erreur de géolocalisation inconnue.';
    switch (err.code) {
      case 1: return 'Géolocalisation refusée. Autorise la position pour ce site dans ton navigateur, puis réessaie.';
      case 2: return 'Position indisponible. Vérifie que le GPS / la localisation est activé sur ton appareil.';
      case 3: return 'La localisation met trop de temps. Réessaie, si possible près d’une fenêtre.';
      default: return 'Erreur de géolocalisation (' + err.message + ').';
    }
  }

  function showGateError(msg) {
    elGateError.textContent = msg;
    elGateError.classList.remove('hidden');
  }

  // ---------- Rejoindre / quitter ----------
  function join() {
    if (joined || joining) return;
    elGateError.classList.add('hidden');

    if (!('geolocation' in navigator)) {
      showGateError('Ton navigateur ne permet pas la géolocalisation.');
      return;
    }
    if (!window.isSecureContext) {
      showGateError('La géolocalisation exige une page en HTTPS.');
      return;
    }

    var name = cleanName(elCallsign.value);
    if (!name) {
      name = randomCallsign();
      elCallsign.value = name;
    }
    try { localStorage.setItem('radar_name', name); } catch (e) {}

    joining = true;
    elJoin.disabled = true;
    elJoin.textContent = 'Acquisition du signal…';

    ensureAuth().then(function (user) {
      myUid = user.uid;
      // Clé de présence propre à CET onglet : deux onglets du même compte
      // ne se suppriment plus mutuellement à la fermeture.
      myPid = user.uid + '-' + newSessionId();
      meRef = db.ref('presence/' + myPid);

      if (watchId !== null) navigator.geolocation.clearWatch(watchId);
      watchId = navigator.geolocation.watchPosition(
        function (fix) {
          lastFix = fix;
          lastFixAt = Date.now();
          if (joining && !joined) {
            // Premier fix : on apparaît
            joining = false;
            joined = true;
            meRef.onDisconnect().remove();
            writeFix(fix, true);
            enterMapMode();
          } else if (joined) {
            writeFix(fix, false);
          }
        },
        function (err) {
          if (!joined) {
            if (watchId !== null) navigator.geolocation.clearWatch(watchId);
            watchId = null;
            joining = false;
            elJoin.disabled = false;
            elJoin.textContent = 'Apparaître sur le radar';
            showGateError(geoErrorMessage(err));
          } else if (err.code === 1) {
            // Permission retirée en cours de route : on ne diffuse pas une
            // position figée comme « live ». Retrait immédiat du radar.
            toast('Localisation coupée — tu as quitté le radar', true);
            quit();
          } else {
            console.warn('[radar] geoloc:', err.message);
          }
        },
        { enableHighAccuracy: true, maximumAge: 5000, timeout: 20000 }
      );
    }).catch(function (err) {
      console.error('[radar] auth:', err);
      joining = false;
      elJoin.disabled = false;
      elJoin.textContent = 'Apparaître sur le radar';
      showGateError('Connexion au radar impossible (' + (err.code || err.message) + '). Réessaie.');
    });
  }

  function enterMapMode() {
    document.body.classList.remove('gated');
    elGate.classList.add('hidden');
    elHud.classList.remove('hidden');
    elRoster.classList.remove('hidden');
    elJoin.disabled = false;
    elJoin.textContent = 'Apparaître sur le radar';

    // Cadrage initial : tout le monde à l'écran si d'autres sont là
    var pts = [];
    var now = serverNow();
    Object.keys(people).forEach(function (uid) {
      var p = people[uid];
      if (p && typeof p.lat === 'number' && now - (p.t || 0) < STALE_MS) pts.push([p.lat, p.lng]);
    });
    if (lastPayload) pts.push([lastPayload.lat, lastPayload.lng]);
    // Étendue réelle des points (évite un fitBounds sur des positions quasi confondues)
    var maxD = 0;
    if (lastPayload) pts.forEach(function (c) { maxD = Math.max(maxD, haversine(lastPayload.lat, lastPayload.lng, c[0], c[1])); });
    suppressMoveEvents = true;
    if (map && pts.length > 1 && maxD > 40) {
      var b = new google.maps.LatLngBounds();
      pts.forEach(function (c) { b.extend({ lat: c[0], lng: c[1] }); });
      map.fitBounds(b, 70);
      follow = false;
    } else if (map && lastPayload) {
      map.panTo({ lat: lastPayload.lat, lng: lastPayload.lng });
      map.setZoom(16);
      follow = true;
    }
    setTimeout(function () { suppressMoveEvents = false; }, 900);

    heartbeatTimer = setInterval(function () {
      // On ne rafraîchit « en direct » QUE si le GPS nous a donné un fix récent.
      // Sinon (onglet en arrière-plan, GPS coupé), on laisse le nœud se périmer
      // puis disparaître : pas de fausse présence figée.
      if (joined && meRef && lastPayload && fixIsFresh()) {
        var refresh = Object.assign({}, lastPayload, { t: firebase.database.ServerValue.TIMESTAMP });
        meRef.set(refresh).catch(function () {});
        lastPayload.t = serverNow();
      }
    }, HEARTBEAT_MS);

    repaint();
  }

  function quit() {
    joined = false;
    joining = false;
    if (watchId !== null) {
      navigator.geolocation.clearWatch(watchId);
      watchId = null;
    }
    clearInterval(heartbeatTimer);
    if (meRef) {
      meRef.onDisconnect().cancel();
      meRef.remove().catch(function () {});
    }
    lastPayload = null;
    lastWriteAt = 0;
    // Réinitialiser l'état rendez-vous
    selectedPid = null;
    meetSamples = [];
    knownIncoming = {};
    clearMeetLine();
    Object.keys(incomingLines).forEach(removeIncomingLine);
    elMeetup.classList.add('hidden');
    document.body.classList.remove('has-meet');
    // Réinitialiser le point de test
    if (testPoint) { testPoint = null; removeMarker(TEST_PID); delete people[TEST_PID]; }
    elTestbox.classList.add('hidden');
    elTestRemove.classList.add('hidden');
    elBtnTest.classList.remove('active');
    if (accCircle) { accCircle.remove(); accCircle = null; }
    follow = true;
    document.body.classList.add('gated');
    elHud.classList.add('hidden');
    elRoster.classList.add('hidden');
    elGate.classList.remove('hidden');
    repaint();
  }

  function share() {
    var data = { title: 'Radar', text: 'Rejoins-moi sur le radar 📡', url: SHARE_URL };
    if (navigator.share) {
      navigator.share(data).catch(function () {});
    } else if (navigator.clipboard) {
      navigator.clipboard.writeText(SHARE_URL).then(function () {
        toast('Lien copié — envoie-le !');
      }).catch(function () {
        toast(SHARE_URL);
      });
    } else {
      toast(SHARE_URL);
    }
  }

  // ---------- Événements UI ----------
  elJoin.addEventListener('click', join);
  elReroll.addEventListener('click', function () {
    elCallsign.value = randomCallsign();
  });
  elCallsign.addEventListener('keydown', function (e) {
    if (e.key === 'Enter') join();
  });
  $('btn-quit').addEventListener('click', quit);
  $('btn-share').addEventListener('click', share);
  $('meet-close').addEventListener('click', function () { clearMeet(); });
  elBtnTest.addEventListener('click', toggleTestbox);
  elTestGo.addEventListener('click', placeTest);
  // Entrée : si Google Places n'a pas déjà placé le point (boîte encore ouverte), géocode le texte
  elTestAddr.addEventListener('keydown', function (e) {
    if (e.key === 'Enter') {
      setTimeout(function () { if (!elTestbox.classList.contains('hidden')) placeTest(); }, 300);
    }
  });
  elTestRemove.addEventListener('click', removeTest);
  $('btn-center').addEventListener('click', function () {
    follow = true;
    if (lastPayload) panTo([lastPayload.lat, lastPayload.lng], Math.max(map.getZoom(), 15));
  });

  // Retour d'onglet : rafraîchir seulement si le dernier fix GPS est récent,
  // sinon demander une position fraîche plutôt que rediffuser une vieille.
  document.addEventListener('visibilitychange', function () {
    if (document.hidden || !joined) return;
    if (fixIsFresh() && lastFix) {
      writeFix(lastFix, true);
    } else if (navigator.geolocation) {
      navigator.geolocation.getCurrentPosition(function (fix) {
        lastFix = fix;
        lastFixAt = Date.now();
        if (joined) writeFix(fix, true);
      }, function () {}, { enableHighAccuracy: true, maximumAge: 0, timeout: 15000 });
    }
  });
  window.addEventListener('pagehide', function () {
    // onDisconnect s'en charge côté serveur ; on tente aussi localement
    if (joined && meRef) meRef.remove().catch(function () {});
  });

  // ---------- Démarrage ----------
  document.body.classList.add('gated');
  var savedName = null;
  try { savedName = localStorage.getItem('radar_name'); } catch (e) {}
  elCallsign.value = savedName || randomCallsign();

  initMap();
  initFirebase();
  repaintTimer = setInterval(repaint, 15000); // fraîcheur des états stale, même avant de rejoindre
})();
